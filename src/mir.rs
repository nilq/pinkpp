use std;
use std::collections::HashMap;
use std::ffi::{CStr, CString};
use llvm_sys::prelude::*;
use llvm_sys::core::*;
use ty::{self, Ty};

const START_BLOCK: Block = Block(0);
const END_BLOCK: Block = Block(1);

#[derive(Debug)]
pub struct Function {
    ty: ty::Function,
    temporaries: Vec<Ty>,
    //locals: HashMap<String, Lvalue>,
    blocks: Vec<BlockData>,
}
#[derive(Copy, Clone, Debug)]
struct Temporary(usize);

impl Function {
    pub fn new(ty: ty::Function) -> Function {
        let mut ret = Function {
            ty: ty,
            temporaries: Vec::new(),
            blocks: Vec::new(),
        };
        assert_eq!(START_BLOCK, ret.new_block());
        assert_eq!(END_BLOCK, ret.new_block());
        END_BLOCK.terminate(&mut ret, Terminator::Return);
        ret
    }

    pub fn start_block(&self) -> Block {
        START_BLOCK
    }

    fn new_block(&mut self) -> Block {
        self.blocks.push(BlockData::new());
        Block(self.blocks.len() - 1)
    }
    fn new_tmp(&mut self, ty: Ty) -> Temporary {
        self.temporaries.push(ty);
        Temporary(self.temporaries.len() - 1)
    }

    fn get_block(&mut self, blk: &Block) -> &mut BlockData {
        &mut self.blocks[blk.0]
    }
    fn get_tmp_ty(&self, tmp: &Temporary) -> Ty {
        self.temporaries[tmp.0]
    }

    fn get_leaf(&mut self, value: Value, block: &Block,
            fn_types: &HashMap<String, ty::Function>) -> ValueLeaf {
        if let ValueKind::Leaf(leaf) = value.0 {
            leaf
        } else {
            let ty = value.ty(self, fn_types);
            let tmp = self.new_tmp(ty);
            let blk = self.get_block(block);
            blk.statements.push(Statement(Lvalue::Temporary(tmp), value));
            ValueLeaf::Temporary(tmp)
        }
    }

    fn build(self, llfunc: LLVMValueRef,
             llvm_funcs: &HashMap<String, LLVMValueRef>) {
        LlFunction::build(self, llfunc, llvm_funcs)
    }
}

struct LlFunction {
    mir: Function,
    //raw: LLVMValueRef,
    builder: LLVMBuilderRef,
    ret_ptr: LLVMValueRef,
    temporaries: Vec<LLVMValueRef>,
    blocks: Vec<LLVMBasicBlockRef>,
}

impl LlFunction {
    fn build(mir: Function, llfunc: LLVMValueRef,
            llvm_funcs: &HashMap<String, LLVMValueRef>) {
        unsafe {
            let builder = LLVMCreateBuilder();
            let mut blocks = Vec::new();
            for i in 0..mir.blocks.len() {
                blocks.push(LLVMAppendBasicBlock(llfunc,
                    CString::new(format!("bb{}", i)).unwrap().as_ptr()));
            }

            LLVMPositionBuilderAtEnd(builder, blocks[0]);

            let mut tmps = Vec::new();
            for mir_tmp in &mir.temporaries {
                tmps.push(LLVMBuildAlloca(builder, mir_tmp.to_llvm(),
                    cstr!("tmp")));
            }

            let ret_ptr = LLVMBuildAlloca(builder, mir.ty.output().to_llvm(),
                cstr!("ret"));

            let mut self_ = LlFunction {
                mir: mir,
                //raw: llfunc,
                builder: builder,
                ret_ptr: ret_ptr,
                temporaries: tmps,
                blocks: blocks,
            };

            let mut i = self_.mir.blocks.len();
            while let Some(blk) = self_.mir.blocks.pop() {
                i -= 1;
                LLVMPositionBuilderAtEnd(self_.builder, self_.blocks[i]);
                for stmt in blk.statements {
                    stmt.to_llvm(&mut self_, llvm_funcs);
                }
                blk.terminator.expect("terminator")
                    .to_llvm(&self_);
            }
        }
    }


    fn get_tmp_ptr(&self, tmp: &Temporary) -> LLVMValueRef {
        self.temporaries[tmp.0]
    }
    fn get_tmp_value(&self, tmp: &Temporary) -> LLVMValueRef {
        unsafe {
            LLVMBuildLoad(self.builder, self.temporaries[tmp.0], cstr!(""))
        }
    }
    fn get_block(&self, blk: &Block) -> LLVMBasicBlockRef {
        self.blocks[blk.0]
    }
}

#[derive(Clone, Debug)]
enum ValueLeaf {
    ConstInt {
        value: u64,
        ty: Ty,
    },
    Temporary(Temporary),
}

impl ValueLeaf {
    fn ty(&self, function: &Function) -> Ty {
        match *self {
            ValueLeaf::ConstInt {
                ty,
                ..
            } => ty,
            ValueLeaf::Temporary(ref tmp) => function.get_tmp_ty(tmp),
        }
    }

    unsafe fn to_llvm(self, function: &LlFunction) -> LLVMValueRef {
        match self {
            ValueLeaf::ConstInt {
                value,
                ty,
            } => {
                LLVMConstInt(ty.to_llvm(), value, false as LLVMBool)
            }
            ValueLeaf::Temporary(tmp) => {
                function.get_tmp_value(&tmp)
            }
        }
    }
}

#[derive(Clone, Debug)]
enum ValueKind {
    Leaf(ValueLeaf),

    // -- unops --
    Pos(ValueLeaf),
    Neg(ValueLeaf),
    Not(ValueLeaf),

    // -- binops --
    Add(ValueLeaf, ValueLeaf),
    Sub(ValueLeaf, ValueLeaf),
    Mul(ValueLeaf, ValueLeaf),
    Div(ValueLeaf, ValueLeaf),
    Rem(ValueLeaf, ValueLeaf),
    And(ValueLeaf, ValueLeaf),
    Xor(ValueLeaf, ValueLeaf),
    Or(ValueLeaf, ValueLeaf),
    Shl(ValueLeaf, ValueLeaf),
    Shr(ValueLeaf, ValueLeaf),

    // -- comparison --
    Eq(ValueLeaf, ValueLeaf),
    Neq(ValueLeaf, ValueLeaf),
    Lt(ValueLeaf, ValueLeaf),
    Lte(ValueLeaf, ValueLeaf),
    Gt(ValueLeaf, ValueLeaf),
    Gte(ValueLeaf, ValueLeaf),

    // -- other --
    Call {
        callee: String,
        args: Vec<ValueLeaf>,
    },
}

#[derive(Clone, Debug)]
pub struct Value(ValueKind);

// --- CONSTRUCTORS ---
impl Value {
    // -- literals --
    pub fn const_int(value: u64, ty: Ty) -> Value {
        Value(ValueKind::Leaf(
            ValueLeaf::ConstInt {
                value: value,
                ty: ty,
            }
        ))
    }

    // -- unops --
    pub fn pos(inner: Value, function: &mut Function, block: &Block,
            fn_types: &HashMap<String, ty::Function>) -> Value {
        Value(ValueKind::Pos(function.get_leaf(inner, block, fn_types)))
    }
    pub fn neg(inner: Value, function: &mut Function, block: &Block,
            fn_types: &HashMap<String, ty::Function>) -> Value {
        Value(ValueKind::Neg(function.get_leaf(inner, block, fn_types)))
    }
    pub fn not(inner: Value, function: &mut Function, block: &Block,
            fn_types: &HashMap<String, ty::Function>) -> Value {
        Value(ValueKind::Not(function.get_leaf(inner, block, fn_types)))
    }

    // -- binops --
    pub fn add(lhs: Value, rhs: Value, function: &mut Function, block: &Block,
            fn_types: &HashMap<String, ty::Function>) -> Value {
        Value(ValueKind::Add(
            function.get_leaf(lhs, block, fn_types),
            function.get_leaf(rhs, block, fn_types)))
    }
    pub fn sub(lhs: Value, rhs: Value, function: &mut Function, block: &Block,
            fn_types: &HashMap<String, ty::Function>) -> Value {
        Value(ValueKind::Sub(
            function.get_leaf(lhs, block, fn_types),
            function.get_leaf(rhs, block, fn_types)))
    }
    pub fn mul(lhs: Value, rhs: Value, function: &mut Function, block: &Block,
            fn_types: &HashMap<String, ty::Function>) -> Value {
        Value(ValueKind::Mul(
            function.get_leaf(lhs, block, fn_types),
            function.get_leaf(rhs, block, fn_types)))
    }
    pub fn div(lhs: Value, rhs: Value, function: &mut Function, block: &Block,
            fn_types: &HashMap<String, ty::Function>) -> Value {
        Value(ValueKind::Div(
            function.get_leaf(lhs, block, fn_types),
            function.get_leaf(rhs, block, fn_types)))
    }
    pub fn rem(lhs: Value, rhs: Value, function: &mut Function, block: &Block,
            fn_types: &HashMap<String, ty::Function>) -> Value {
        Value(ValueKind::Rem(
            function.get_leaf(lhs, block, fn_types),
            function.get_leaf(rhs, block, fn_types)))
    }
    pub fn and(lhs: Value, rhs: Value, function: &mut Function, block: &Block,
            fn_types: &HashMap<String, ty::Function>) -> Value {
        Value(ValueKind::And(
            function.get_leaf(lhs, block, fn_types),
            function.get_leaf(rhs, block, fn_types)))
    }
    pub fn xor(lhs: Value, rhs: Value, function: &mut Function, block: &Block,
            fn_types: &HashMap<String, ty::Function>) -> Value {
        Value(ValueKind::Xor(
            function.get_leaf(lhs, block, fn_types),
            function.get_leaf(rhs, block, fn_types)))
    }
    pub fn or(lhs: Value, rhs: Value, function: &mut Function, block: &Block,
            fn_types: &HashMap<String, ty::Function>) -> Value {
        Value(ValueKind::Or(
            function.get_leaf(lhs, block, fn_types),
            function.get_leaf(rhs, block, fn_types)))
    }
    pub fn shl(lhs: Value, rhs: Value, function: &mut Function, block: &Block,
            fn_types: &HashMap<String, ty::Function>) -> Value {
        Value(ValueKind::Shl(
            function.get_leaf(lhs, block, fn_types),
            function.get_leaf(rhs, block, fn_types)))
    }
    pub fn shr(lhs: Value, rhs: Value, function: &mut Function, block: &Block,
            fn_types: &HashMap<String, ty::Function>) -> Value {
        Value(ValueKind::Shr(
            function.get_leaf(lhs, block, fn_types),
            function.get_leaf(rhs, block, fn_types)))
    }

    // -- comparisons --
    pub fn eq(lhs: Value, rhs: Value, function: &mut Function, block: &Block,
            fn_types: &HashMap<String, ty::Function>) -> Value {
        Value(ValueKind::Eq(
            function.get_leaf(lhs, block, fn_types),
            function.get_leaf(rhs, block, fn_types)))
    }
    pub fn neq(lhs: Value, rhs: Value, function: &mut Function, block: &Block,
            fn_types: &HashMap<String, ty::Function>) -> Value {
        Value(ValueKind::Neq(
            function.get_leaf(lhs, block, fn_types),
            function.get_leaf(rhs, block, fn_types)))
    }
    pub fn lt(lhs: Value, rhs: Value, function: &mut Function, block: &Block,
            fn_types: &HashMap<String, ty::Function>) -> Value {
        Value(ValueKind::Lt(
            function.get_leaf(lhs, block, fn_types),
            function.get_leaf(rhs, block, fn_types)))
    }
    pub fn lte(lhs: Value, rhs: Value, function: &mut Function, block: &Block,
            fn_types: &HashMap<String, ty::Function>) -> Value {
        Value(ValueKind::Lte(
            function.get_leaf(lhs, block, fn_types),
            function.get_leaf(rhs, block, fn_types)))
    }
    pub fn gt(lhs: Value, rhs: Value, function: &mut Function, block: &Block,
            fn_types: &HashMap<String, ty::Function>) -> Value {
        Value(ValueKind::Gt(
            function.get_leaf(lhs, block, fn_types),
            function.get_leaf(rhs, block, fn_types)))
    }
    pub fn gte(lhs: Value, rhs: Value, function: &mut Function, block: &Block,
            fn_types: &HashMap<String, ty::Function>) -> Value {
        Value(ValueKind::Gte(
            function.get_leaf(lhs, block, fn_types),
            function.get_leaf(rhs, block, fn_types)))
    }

    // -- misc --
    pub fn call(callee: String, args: Vec<Value>, function: &mut Function,
            block: &Block, fn_types: &HashMap<String, ty::Function>) -> Value {
        let args =
            args.into_iter().map(|v|
                function.get_leaf(v, block, fn_types)).collect();
        Value(ValueKind::Call {
            callee: callee,
            args: args,
        })
    }
}

impl Value {
    fn ty(&self, function: &Function, fn_types: &HashMap<String, ty::Function>)
            -> Ty {
        match self.0 {
            ValueKind::Leaf(ref v) => v.ty(function),

            ValueKind::Pos(ref inner) | ValueKind::Neg(ref inner)
            | ValueKind::Not(ref inner) => inner.ty(function),

            ValueKind::Add(ref lhs, ref rhs)
            | ValueKind::Sub(ref lhs, ref rhs)
            | ValueKind::Mul(ref lhs, ref rhs)
            | ValueKind::Div(ref lhs, ref rhs)
            | ValueKind::Rem(ref lhs, ref rhs)
            | ValueKind::And(ref lhs, ref rhs)
            | ValueKind::Xor(ref lhs, ref rhs)
            | ValueKind::Or(ref lhs, ref rhs)
            => {
                let lhs_ty = lhs.ty(function);
                assert_eq!(lhs_ty, rhs.ty(function));
                lhs_ty
            }

            ValueKind::Shl(ref lhs, _)
            | ValueKind::Shr(ref lhs, _)
            => {
                lhs.ty(function)
            }

            ValueKind::Eq(_, _) | ValueKind::Neq(_, _) | ValueKind::Lt(_, _)
            | ValueKind::Lte(_, _) | ValueKind::Gt(_, _) | ValueKind::Gte(_, _)
                => Ty::Bool,

            ValueKind::Call {
                ref callee,
                ..
            } =>  {
                fn_types.get(callee).expect("ICE: no function prototype")
                    .output()
            }
        }
    }

    unsafe fn to_llvm(self, function: &mut LlFunction,
            llvm_funcs: &HashMap<String, LLVMValueRef>) -> LLVMValueRef {
        use llvm_sys::LLVMIntPredicate::*;
        match self.0 {
            ValueKind::Leaf(v) => {
                v.to_llvm(function)
            }
            ValueKind::Pos(inner) => {
                let ty = inner.ty(&function.mir);
                let llinner = inner.to_llvm(function);
                match ty {
                    Ty::SInt(_) | Ty::UInt(_) => llinner,
                    ty => panic!("ICE: {} can't be used in unary +", ty),
                }
            }
            ValueKind::Neg(inner) => {
                // TODO(ubsan): check types
                let ty = inner.ty(&function.mir);
                let llinner = inner.to_llvm(function);
                match ty {
                    Ty::SInt(_) =>
                        LLVMBuildNeg(function.builder, llinner, cstr!("")),
                    ty => panic!("ICE: {} can't be used in unary -", ty),
                }
            }
            ValueKind::Not(inner) => {
                let ty = inner.ty(&function.mir);
                let llinner = inner.to_llvm(function);
                match ty {
                    Ty::SInt(_) | Ty::UInt(_) | Ty::Bool =>
                        LLVMBuildNot(function.builder, llinner, cstr!("")),
                    ty => panic!("ICE: {} can't be used in unary !", ty),
                }
            }
            ValueKind::Add(lhs, rhs) => {
                let ty = lhs.ty(&function.mir);
                let lhs = lhs.to_llvm(function);
                let rhs = rhs.to_llvm(function);
                match ty {
                    Ty::SInt(_) | Ty::UInt(_) =>
                        LLVMBuildAdd(function.builder, lhs, rhs, cstr!("")),
                    ty => panic!("ICE: {} can't be used in binary +", ty),
                }
            }
            ValueKind::Sub(lhs, rhs) => {
                let ty = lhs.ty(&function.mir);
                let lhs = lhs.to_llvm(function);
                let rhs = rhs.to_llvm(function);
                match ty {
                    Ty::SInt(_) | Ty::UInt(_) =>
                        LLVMBuildSub(function.builder, lhs, rhs, cstr!("")),
                    ty => panic!("ICE: {} can't be used in binary -", ty),
                }
            }
            ValueKind::Mul(lhs, rhs) => {
                let ty = lhs.ty(&function.mir);
                let lhs = lhs.to_llvm(function);
                let rhs = rhs.to_llvm(function);
                match ty {
                    Ty::SInt(_) | Ty::UInt(_) =>
                        LLVMBuildMul(function.builder, lhs, rhs, cstr!("")),
                    ty => panic!("ICE: {} can't be used in binary *", ty),
                }
            }
            ValueKind::Div(lhs, rhs) => {
                let ty = lhs.ty(&function.mir);
                let lhs = lhs.to_llvm(function);
                let rhs = rhs.to_llvm(function);
                match ty {
                    Ty::SInt(_) =>
                        LLVMBuildSDiv(function.builder, lhs, rhs, cstr!("")),
                    Ty::UInt(_) =>
                        LLVMBuildUDiv(function.builder, lhs, rhs, cstr!("")),
                    ty => panic!("ICE: {} can't be used in binary /", ty),
                }
            }
            ValueKind::Rem(lhs, rhs) => {
                let ty = lhs.ty(&function.mir);
                let lhs = lhs.to_llvm(function);
                let rhs = rhs.to_llvm(function);
                match ty {
                    Ty::SInt(_) =>
                        LLVMBuildSRem(function.builder, lhs, rhs, cstr!("")),
                    Ty::UInt(_) =>
                        LLVMBuildURem(function.builder, lhs, rhs, cstr!("")),
                    ty => panic!("ICE: {} can't be used in binary %", ty),
                }
            }
            ValueKind::And(lhs, rhs) => {
                let ty = lhs.ty(&function.mir);
                let lhs = lhs.to_llvm(function);
                let rhs = rhs.to_llvm(function);
                match ty {
                    Ty::SInt(_) | Ty::UInt(_) | Ty::Bool =>
                        LLVMBuildAnd(function.builder, lhs, rhs, cstr!("")),
                    ty => panic!("ICE: {} can't be used in binary %", ty),
                }
            }
            ValueKind::Xor(lhs, rhs) => {
                let ty = lhs.ty(&function.mir);
                let lhs = lhs.to_llvm(function);
                let rhs = rhs.to_llvm(function);
                match ty {
                    Ty::SInt(_) | Ty::UInt(_) | Ty::Bool =>
                        LLVMBuildXor(function.builder, lhs, rhs, cstr!("")),
                    ty => panic!("ICE: {} can't be used in binary %", ty),
                }
            }
            ValueKind::Or(lhs, rhs) => {
                let ty = lhs.ty(&function.mir);
                let lhs = lhs.to_llvm(function);
                let rhs = rhs.to_llvm(function);
                match ty {
                    Ty::SInt(_) | Ty::UInt(_) | Ty::Bool =>
                        LLVMBuildOr(function.builder, lhs, rhs, cstr!("")),
                    ty => panic!("ICE: {} can't be used in binary %", ty),
                }
            }
            ValueKind::Shl(lhs, rhs) => {
                let ty = lhs.ty(&function.mir);
                let lhs = lhs.to_llvm(function);
                let rhs = rhs.to_llvm(function);
                match ty {
                    Ty::SInt(_) | Ty::UInt(_) =>
                        LLVMBuildShl(function.builder, lhs, rhs, cstr!("")),
                    ty => panic!("ICE: {} can't be used in binary %", ty),
                }
            }
            ValueKind::Shr(lhs, rhs) => {
                let ty = lhs.ty(&function.mir);
                let lhs = lhs.to_llvm(function);
                let rhs = rhs.to_llvm(function);
                match ty {
                    Ty::SInt(_) =>
                        LLVMBuildAShr(function.builder, lhs, rhs, cstr!("")),
                    Ty::UInt(_) =>
                        LLVMBuildLShr(function.builder, lhs, rhs, cstr!("")),
                    ty => panic!("ICE: {} can't be used in binary %", ty),
                }
            }
            ValueKind::Eq(lhs, rhs) => {
                let ty = lhs.ty(&function.mir);
                let lhs = lhs.to_llvm(function);
                let rhs = rhs.to_llvm(function);
                match ty {
                    Ty::SInt(_) | Ty::UInt(_) | Ty::Bool =>
                        LLVMBuildICmp(function.builder, LLVMIntEQ,
                            lhs, rhs, cstr!("")),
                    ty =>  panic!("ICE: {} can't be used in ==", ty),
                }
            }
            ValueKind::Neq(lhs, rhs) => {
                let ty = lhs.ty(&function.mir);
                let lhs = lhs.to_llvm(function);
                let rhs = rhs.to_llvm(function);
                match ty {
                    Ty::SInt(_) | Ty::UInt(_) | Ty::Bool =>
                        LLVMBuildICmp(function.builder, LLVMIntNE,
                            lhs, rhs, cstr!("")),
                    ty =>  panic!("ICE: {} can't be used in ==", ty),
                }
            }
            ValueKind::Lt(lhs, rhs) => {
                let ty = lhs.ty(&function.mir);
                let lhs = lhs.to_llvm(function);
                let rhs = rhs.to_llvm(function);
                match ty {
                    Ty::SInt(_) =>
                        LLVMBuildICmp(function.builder, LLVMIntSLT,
                            lhs, rhs, cstr!("")),
                    Ty::UInt(_) | Ty::Bool =>
                        LLVMBuildICmp(function.builder, LLVMIntULT,
                            lhs, rhs, cstr!("")),
                    ty =>  panic!("ICE: {} can't be used in ==", ty),
                }
            }
            ValueKind::Lte(lhs, rhs) => {
                let ty = lhs.ty(&function.mir);
                let lhs = lhs.to_llvm(function);
                let rhs = rhs.to_llvm(function);
                match ty {
                    Ty::SInt(_) =>
                        LLVMBuildICmp(function.builder, LLVMIntSLE,
                            lhs, rhs, cstr!("")),
                    Ty::UInt(_) | Ty::Bool =>
                        LLVMBuildICmp(function.builder, LLVMIntULE,
                            lhs, rhs, cstr!("")),
                    ty =>  panic!("ICE: {} can't be used in ==", ty),
                }
            }
            ValueKind::Gt(lhs, rhs) => {
                let ty = lhs.ty(&function.mir);
                let lhs = lhs.to_llvm(function);
                let rhs = rhs.to_llvm(function);
                match ty {
                    Ty::SInt(_) =>
                        LLVMBuildICmp(function.builder, LLVMIntSGT,
                            lhs, rhs, cstr!("")),
                    Ty::UInt(_) | Ty::Bool =>
                        LLVMBuildICmp(function.builder, LLVMIntUGT,
                            lhs, rhs, cstr!("")),
                    ty =>  panic!("ICE: {} can't be used in ==", ty),
                }
            }
            ValueKind::Gte(lhs, rhs) => {
                let ty = lhs.ty(&function.mir);
                let lhs = lhs.to_llvm(function);
                let rhs = rhs.to_llvm(function);
                match ty {
                    Ty::SInt(_) =>
                        LLVMBuildICmp(function.builder, LLVMIntSGE,
                            lhs, rhs, cstr!("")),
                    Ty::UInt(_) | Ty::Bool =>
                        LLVMBuildICmp(function.builder, LLVMIntUGE,
                            lhs, rhs, cstr!("")),
                    ty =>  panic!("ICE: {} can't be used in ==", ty),
                }
            }
            ValueKind::Call {
                callee,
                args,
            } => {
                let mut args = args.into_iter().map(|a| a.to_llvm(function))
                    .collect::<Vec<_>>();
                let callee = *llvm_funcs.get(&callee).unwrap();
                LLVMBuildCall(function.builder, callee, args.as_mut_ptr(),
                    args.len() as u32, cstr!(""))
            }
        }
    }
}

#[derive(Copy, Clone, Debug)]
enum Lvalue {
    Temporary(Temporary),
    Return,
}

#[derive(Debug)]
struct Statement(Lvalue, Value);

impl Statement {
    unsafe fn to_llvm(self, function: &mut LlFunction,
            llvm_funcs: &HashMap<String, LLVMValueRef>) {
        let dst = match self.0 {
            Lvalue::Return => function.ret_ptr,
            Lvalue::Temporary(tmp) => function.get_tmp_ptr(&tmp),
        };
        LLVMBuildStore(function.builder,
            (self.1).to_llvm(function, llvm_funcs), dst);
    }
}

#[derive(Debug)]
enum Terminator {
    Goto(Block),
    // Normal return; should only happen in the end block
    Return,
}

impl Terminator {
    unsafe fn to_llvm(self, function: &LlFunction) {
        match self {
            Terminator::Goto(b) => {
                LLVMBuildBr(function.builder, function.get_block(&b));
            },
            Terminator::Return => {
                let value = LLVMBuildLoad(function.builder,
                    function.ret_ptr, cstr!(""));
                LLVMBuildRet(function.builder, value);
            }
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Block(usize);

impl Block {
    pub fn ret(self, function: &mut Function, value: Value) {
        let blk = function.get_block(&self);
        blk.statements.push(Statement(Lvalue::Return, value));
        blk.terminator = Some(Terminator::Goto(END_BLOCK));
    }

    fn terminate(&self, function: &mut Function, terminator: Terminator) {
        let blk = function.get_block(self);
        blk.terminator = Some(terminator);
    }
}

#[derive(Debug)]
struct BlockData {
    statements: Vec<Statement>,
    terminator: Option<Terminator>,
}

impl BlockData {
    fn new() -> BlockData {
        BlockData {
            statements: Vec::new(),
            terminator: None,
        }
    }
}

#[derive(Debug)]
pub struct Mir {
    functions: HashMap<String, Function>,
}

impl Mir {
    pub fn new() -> Mir {
        Mir {
            functions: HashMap::new(),
        }
    }

    pub fn add_function(&mut self, name: String, func: Function) {
        self.functions.insert(name, func);
    }

    pub fn build(self) {
        unsafe {
            let mut main_output = None;
            let mut llvm_functions = HashMap::new();
            let module = LLVMModuleCreateWithName(cstr!(""));
            for (name, function) in &self.functions {
                if name == "main" {
                    main_output = Some(function.ty.output());
                }
                let llfunc = LLVMAddFunction(module,
                    CString::new(name.clone()).unwrap().as_ptr(),
                    function.ty.to_llvm());
                llvm_functions.insert(name.clone(), llfunc);
            }

            for (name, function) in self.functions {
                let llfunc = *llvm_functions.get(&name).unwrap();
                function.build(llfunc, &llvm_functions);
            }

            if let Some(f) = llvm_functions.get("main") {
                Self::run(main_output.unwrap(), module, *f)
            }
        }
    }

    unsafe fn run(ty: Ty, module: LLVMModuleRef, function: LLVMValueRef) {
        use llvm_sys::analysis::*;
        use llvm_sys::execution_engine::*;
        use llvm_sys::target::*;
        use std::io::Write;

        LLVMDumpModule(module);

        let mut error: *mut i8 = std::mem::uninitialized();
        LLVMVerifyModule(module,
            LLVMVerifierFailureAction::LLVMAbortProcessAction, &mut error);
        LLVMDisposeMessage(error);

        println!("--- RUNNING ---");
        let mut engine: LLVMExecutionEngineRef = std::mem::uninitialized();
        error = std::ptr::null_mut();
        LLVMLinkInMCJIT();
        LLVM_InitializeNativeTarget();
        LLVM_InitializeNativeAsmPrinter();
        if LLVMCreateJITCompilerForModule(&mut engine, module,
                0, &mut error) != 0 {
            writeln!(std::io::stderr(),
                "failed to create execution engine: {:?}",
                CStr::from_ptr(error)).unwrap();
            LLVMDisposeMessage(error);
            std::process::exit(-1);
        }

        let res = LLVMRunFunction(engine, function, 0, std::ptr::null_mut());
        match ty {
            Ty::SInt(ty::Int::I32) => {
                let val = LLVMGenericValueToInt(res, true as LLVMBool);
                println!("{}", val as i32);
            }
            Ty::UInt(ty::Int::I32) => {
                let val = LLVMGenericValueToInt(res, true as LLVMBool);
                println!("{}", val as u32);
            }
            Ty::Unit => {}
            ref ty => {
                println!("Pink does not yet support printing the \
                    {:?} return type", ty);
            }
        }

        LLVMDisposeGenericValue(res);
        LLVMDisposeExecutionEngine(engine);
    }
}

impl std::fmt::Display for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        for (i, tmp) in self.temporaries.iter().enumerate() {
            try!(writeln!(f, "  let tmp{}: {};", i, tmp));
        }
        for (i, block) in self.blocks.iter().enumerate() {
            try!(writeln!(f, "  bb{}: {{", i));
            for stmt in &block.statements {
                try!(writeln!(f, "    {};", stmt));
            }
            if let Some(ref t) = block.terminator {
                try!(writeln!(f, "    {};", t));
            }
            try!(writeln!(f, "  }}"));
        }
        Ok(())
    }
}

impl std::fmt::Display for Terminator {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match *self {
            Terminator::Goto(ref b) => write!(f, "goto -> bb{}", b.0),
            Terminator::Return => write!(f, "return"),
        }
    }
}

impl std::fmt::Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "{} = {}", self.0, self.1)
    }
}

impl std::fmt::Display for Lvalue {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match *self {
            Lvalue::Return => write!(f, "return"),
            Lvalue::Temporary(ref tmp) => write!(f, "tmp{}", tmp.0),
        }
    }
}

impl std::fmt::Display for ValueLeaf {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match *self {
            ValueLeaf::ConstInt {
                value,
                ty,
            } => {
                match ty {
                    Ty::UInt(_) => write!(f, "const {}{}", value, ty),
                    Ty::SInt(_) => write!(f, "const {}{}", value as i64, ty),
                    ty => panic!("ICE: non-integer typed integer: {}", ty),
                }
            },
            ValueLeaf::Temporary(ref tmp) => write!(f, "tmp{}", tmp.0),
        }
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match self.0 {
            ValueKind::Leaf(ref v) => write!(f, "{}", v),
            ValueKind::Pos(ref inner) => write!(f, "Pos({})", inner),
            ValueKind::Neg(ref inner) => write!(f, "Neg({})", inner),
            ValueKind::Not(ref inner) => write!(f, "Not({})", inner),
            ValueKind::Add(ref lhs, ref rhs)
                => write!(f, "Add({}, {})", lhs, rhs),
            ValueKind::Sub(ref lhs, ref rhs)
                => write!(f, "Sub({}, {})", lhs, rhs),
            ValueKind::Mul(ref lhs, ref rhs)
                => write!(f, "Mul({}, {})", lhs, rhs),
            ValueKind::Div(ref lhs, ref rhs)
                => write!(f, "Div({}, {})", lhs, rhs),
            ValueKind::Rem(ref lhs, ref rhs)
                => write!(f, "Rem({}, {})", lhs, rhs),
            ValueKind::And(ref lhs, ref rhs)
                => write!(f, "And({}, {})", lhs, rhs),
            ValueKind::Xor(ref lhs, ref rhs)
                => write!(f, "And({}, {})", lhs, rhs),
            ValueKind::Or(ref lhs, ref rhs)
                => write!(f, "And({}, {})", lhs, rhs),
            ValueKind::Shl(ref lhs, ref rhs)
                => write!(f, "Shl({}, {})", lhs, rhs),
            ValueKind::Shr(ref lhs, ref rhs)
                => write!(f, "Shr({}, {})", lhs, rhs),

            ValueKind::Eq(ref lhs, ref rhs)
                => write!(f, "Eq({}, {})", lhs, rhs),
            ValueKind::Neq(ref lhs, ref rhs)
                => write!(f, "Neq({}, {})", lhs, rhs),
            ValueKind::Lt(ref lhs, ref rhs)
                => write!(f, "Lt({}, {})", lhs, rhs),
            ValueKind::Lte(ref lhs, ref rhs)
                => write!(f, "Lte({}, {})", lhs, rhs),
            ValueKind::Gt(ref lhs, ref rhs)
                => write!(f, "Gt({}, {})", lhs, rhs),
            ValueKind::Gte(ref lhs, ref rhs)
                => write!(f, "Gte({}, {})", lhs, rhs),

            ValueKind::Call {
                ref callee,
                ref args,
            } => {
                try!(write!(f, "{}(", callee));
                if args.len() != 0 {
                    for arg in &args[..args.len() - 1] {
                        try!(write!(f, "{}, ", arg));
                    }
                    try!(write!(f, "{}", args[args.len() - 1]));
                }
                write!(f, ")")
            }
        }
    }
}

impl std::fmt::Display for Mir {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        for (name, function) in &self.functions {
            try!(write!(f, "fn {}(", name));
            let inputs = function.ty.input();
            if inputs.len() != 0 {
                for input in &inputs[..inputs.len() - 1] {
                    try!(write!(f, "{}, ", input));
                }
                try!(write!(f, "{}", inputs[inputs.len() - 1]));
            }
            try!(writeln!(f, ") -> {} {{", function.ty.output()));
            try!(writeln!(f, "{}", function));
            try!(writeln!(f, "}}"));
        }
        Ok(())
    }
}

/*
#[derive(Debug)]
struct module {
    raw: LLVMModuleRef,
    opt: LLVMPassManagerRef,
}

impl module {
    fn new(name: &str) -> module {
        use llvm_sys::transforms::scalar::*;
        unsafe {
            let raw = LLVMModuleCreateWithName(CString::new(name)
                .expect("passed a string with a nul to module::new").as_ptr());
            let opt = LLVMCreateFunctionPassManagerForModule(raw);

            // NOTE(ubsan): add optimizations here
            LLVMAddBasicAliasAnalysisPass(opt);
            LLVMAddInstructionCombiningPass(opt);
            LLVMAddReassociatePass(opt);
            LLVMAddGVNPass(opt);
            LLVMAddCFGSimplificationPass(opt);
            LLVMAddDeadStoreEliminationPass(opt);

            LLVMInitializeFunctionPassManager(opt);

            module {
                raw: raw,
                opt: opt,
            }
        }
    }

    unsafe fn add_func(&self, name: &str, ret_ty: &ty, args: &[LLVMTypeRef])
            -> LLVMValueRef {
        let ty = LLVMFunctionType(ret_ty.to_llvm_ret(),
            args.as_ptr() as *mut _, args.len() as u32, false as LLVMBool);
        LLVMAddFunction(self.raw, CString::new(name.to_owned())
            .expect("name should not have a nul in it").as_ptr(), ty)
    }

    fn optimize_function(&self, func: &function) {
        unsafe {
            LLVMVerifyFunction(func.raw, LLVMAbortProcessAction);
            LLVMRunFunctionPassManager(self.opt, func.raw);
        }
    }
}
*/

