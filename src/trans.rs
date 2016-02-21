use std;
use std::collections::HashMap;
use std::ffi::{ CString, CStr };
use parse::{ lexer, operand, parser, parser_error, ty, int };

use llvm_sys::LLVMIntPredicate::*;
use llvm_sys::execution_engine::*;
use llvm_sys::target::*;
use llvm_sys::prelude::*;
use llvm_sys::analysis::*;
use llvm_sys::analysis::LLVMVerifierFailureAction::*;
use llvm_sys::core::*;

// TODO(ubsan): start taking &mut self?


#[derive(Debug)]
pub enum expr {
    Call {
        name: String,
        args: Vec<expr>
    },
    If {
        condition: Box<expr>,
        then_value: Box<expr>,
        else_value: Box<expr>,
    },
    Binop {
        op: operand,
        lhs: Box<expr>,
        rhs: Box<expr>,
    },
    Plus(Box<expr>), // unary plus
    Minus(Box<expr>), // unary minus
    Not(Box<expr>), // !expr
    Variable(String),
    IntLiteral(u64),
    BoolLiteral(bool),
}

impl expr {
    fn translate(self, ty: ty, function: &function, locals: &HashMap<String, value>,
            builder: LLVMBuilderRef, ast: &ast) -> Result<value, ast_error> {
        unsafe {
            match self {
                expr::IntLiteral(i) => {
                    value::int_literal(ty, i)
                }
                expr::BoolLiteral(b) => {
                    value::bool_literal(ty, b)
                }
                expr::Variable(ref name) => {
                    if let Some(val) = locals.get(name) {
                        if val.ty == ty {
                            Ok(val.clone())
                        } else {
                            Err(ast_error::IncorrectType {
                                expected: ty,
                                found: val.ty.clone(),
                                compiler: fl!(),
                            })
                        }
                    } else {
                        value::parameter(ty.clone(), function, name)
                    }
                }
                expr::Binop {
                    op: operand::OrOr,
                    lhs,
                    rhs,
                } => {
                    expr::If {
                        condition: lhs,
                        then_value: Box::new(expr::BoolLiteral(true)),
                        else_value: rhs,
                    }.translate(ty, function, locals, builder, ast)
                }
                expr::Binop {
                    op: operand::AndAnd,
                    lhs,
                    rhs,
                } => {
                    expr::If {
                        condition: Box::new(expr::Not(lhs)),
                        then_value: Box::new(expr::BoolLiteral(false)),
                        else_value: rhs,
                    }.translate(ty, function, locals, builder, ast)
                }
                expr::Binop {
                    op,
                    lhs,
                    rhs,
                } => {
                    let lhs = try!(lhs.translate(ty::Generic, function, locals, builder, ast));
                    let rhs = try!(rhs.translate(ty::Generic, function, locals, builder, ast));
                    value::binop(ty, &op, lhs, rhs, builder)
                }
                expr::Plus(inner) => {
                    inner.translate(ty, function, locals, builder, ast)
                }
                expr::Minus(inner) => {
                    inner.translate(ty.clone(), function, locals, builder, ast)
                        .and_then(|v| v.neg(builder, ty))
                }
                expr::Not(inner) => {
                    inner.translate(ty.clone(), function, locals, builder, ast)
                        .and_then(|v| v.not(builder, ty))
                }
                expr::If {
                    condition,
                    then_value,
                    else_value,
                } => {
                    let then_blk = LLVMAppendBasicBlock(function.raw, cstr!("then"));
                    let else_blk = LLVMAppendBasicBlock(function.raw, cstr!("else"));
                    let join_blk = LLVMAppendBasicBlock(function.raw, cstr!("join"));

                    let cond = try!(condition.translate(ty::Bool, function, locals, builder, ast));
                    LLVMBuildCondBr(builder, cond.raw, then_blk, else_blk);

                    // TODO(ubsan): builder wrapping class
                    LLVMPositionBuilderAtEnd(builder, then_blk);
                    let then_res = try!(then_value.translate(ty.clone(), function, locals, builder, ast));
                    let then_end_blk = LLVMGetInsertBlock(builder);
                    LLVMBuildBr(builder, join_blk);

                    LLVMPositionBuilderAtEnd(builder, else_blk);
                    let else_res = try!(else_value.translate(ty.clone(), function, locals, builder, ast));
                    let else_end_blk = LLVMGetInsertBlock(builder);
                    LLVMBuildBr(builder, join_blk);

                    LLVMPositionBuilderAtEnd(builder, join_blk);
                    let res = LLVMBuildPhi(builder, ty.to_llvm(), cstr!(""));
                    let mut phi_vals = [then_res.raw, else_res.raw];
                    let mut preds = [then_end_blk, else_end_blk];
                    LLVMAddIncoming(res, phi_vals.as_mut_ptr(), preds.as_mut_ptr(), 2);

                    Ok(value { ty: ty, raw: res })
                }
                expr::Call {
                    name,
                    args,
                } => {
                    let mut llvm_args = Vec::new();
                    //let fn_params = ast.fn_params(&name);
                    for (arg, ty) in args.into_iter().zip(try!(ast.fn_params(&name)).iter()) {
                        llvm_args.push(try!(arg.translate(ty.clone(), function, locals, builder, ast)));
                    }
                    ast.call(ty, &name, builder, llvm_args)
                }
            }
        }
    }
}

#[derive(Debug)]
pub enum stmt {
    Return(Option<expr>),
    Let {
        name: String,
        ty: ty,
        value: expr,
    },
}

#[derive(Debug)]
pub enum item {
    Function {
        name: String,
        ret: ty,
        args: Vec<(String, ty)>,
        body: Vec<stmt>,
    }
}

struct function {
    dbg_name: String,
    args: HashMap<String, (usize, ty)>,
    ret_ty: ty,
    args_ty: Vec<ty>,
    raw: LLVMValueRef,
}

impl function {
    fn new(name: String, ret_ty: ty, args: Vec<(String, ty)>, module: LLVMModuleRef)
            -> Result<function, parser_error> {
        let mut args_ty = Vec::new();
        let mut args_hashmap = HashMap::new();
        let mut arg_index = 0;

        let raw = unsafe {
            let mut params_ty = args.iter().map(|&(_, ref t)| t.to_llvm()).collect::<Vec<_>>();
            let function_ty = LLVMFunctionType(ret_ty.to_llvm_ret(), params_ty.as_mut_ptr(),
                params_ty.len() as u32, false as LLVMBool);

            LLVMAddFunction(module, CString::new(name.clone())
                .expect("name should not have a nul in it").as_ptr(), function_ty)
        };

        for (arg_name, arg_ty) in args {
            if !args_hashmap.contains_key(&arg_name) {
                args_ty.push(arg_ty.clone());
                debug_assert!(args_hashmap.insert(arg_name, (arg_index, arg_ty)).is_none());
                arg_index += 1;
            } else {
                return Err(parser_error::DuplicatedFunctionArgument {
                    argument: arg_name,
                    function: name,
                    compiler: fl!(),
                });
            }
        }

        Ok(function {
            dbg_name: name,
            args: args_hashmap,
            ret_ty: ret_ty,
            args_ty: args_ty,
            raw: raw,
        })
    }

    fn add_body(&self, body: Vec<stmt>, ast: &ast) -> Result<(), ast_error> {
        unsafe {
            let bb = LLVMAppendBasicBlock(self.raw, cstr!("entry"));
            let builder = LLVMCreateBuilder();
            LLVMPositionBuilderAtEnd(builder, bb);

            let mut locals = HashMap::new();

            for st in body {
                match st {
                    stmt::Let {
                        name,
                        ty,
                        value,
                    } => {
                        let local = try!(value.translate(ty, self, &locals, builder, ast));
                        locals.insert(name, local);
                    }
                    stmt::Return(expr) => {
                        if let Some(e) = expr {
                            // return expr;
                            let tmp = try!(e.translate(self.ret_ty.clone(),
                                self, &locals, builder, ast));
                            debug_assert!(self.ret_ty == tmp.ty,
                                "ret: {:?} != tmp: {:?}", self.ret_ty, tmp.ty);
                            if self.ret_ty == ty::Unit {
                                LLVMBuildRetVoid(builder);
                            } else {
                                LLVMBuildRet(builder, tmp.raw);
                            }
                        } else {
                            // return;
                            if self.ret_ty == ty::Unit {
                                LLVMBuildRetVoid(builder);
                            } else {
                                return Err(ast_error::IncorrectType {
                                    expected: self.ret_ty.clone(),
                                    found: ty::Unit,
                                    compiler: fl!(),
                                });
                            }
                        }
                    }
                }
            }
            LLVMDisposeBuilder(builder);
        }
        Ok(())
    }
}

#[derive(Debug)]
pub enum ast_error {
    IncorrectNumberOfArguments {
        passed: usize,
        expected: usize,
        function: String,
    },
    UndefinedVariableName {
        name: String,
        function: String,
    },
    FunctionDoesntExist(String),
    IncorrectType {
        expected: ty,
        found: ty,
        compiler: (&'static str, u32),
    },
    BinopUnsupported {
        op: operand,
        lhs: ty,
        rhs: ty,
    },
    UnopUnsupported {
        op: operand,
        inner: ty,
    },
}

pub struct ast {
    functions: HashMap<String, function>,
    function_blocks: HashMap<String, Vec<stmt>>,
    module: module,
}

impl ast {
    pub fn create(lexer: lexer) -> Result<ast, parser_error> {
        let mut parser = parser::new(lexer);
        let mut functions = HashMap::new();
        let mut function_blocks = HashMap::new();
        let module = module::new("test");

        loop {
            match parser.item() {
                Ok(item::Function {
                    name,
                    ret,
                    args,
                    body,
                }) => {
                    if let Some(_) = functions.insert(name.clone(),
                            try!(function::new(name.clone(), ret, args, module.raw))) {
                        return Err(parser_error::DuplicatedFunction {
                            function: name,
                            compiler: fl!(),
                        });
                    }
                    function_blocks.insert(name, body);
                }

                Err(parser_error::ExpectedEof) => break,
                Err(e) => return Err(e),
            }
        }

        Ok(ast {
            functions: functions,
            function_blocks: function_blocks,
            module: module,
        })
    }

    pub fn build(mut self) -> Result<(), ast_error> {
        use std::io::Write;
        assert!(self.function_blocks.len() == self.functions.len());
        for (name, func) in self.functions.iter() {
            match self.function_blocks.remove(name) {
                Some(body) => try!(func.add_body(body, &self)),
                None => panic!("function without an associated block: {}", name),
            }
        }

        unsafe {
            let mut error: *mut i8 = std::mem::uninitialized();
            LLVMVerifyModule(self.module.raw, LLVMAbortProcessAction, &mut error);
            LLVMDisposeMessage(error);

            if let Some(main) = self.functions.get("main") {
                if main.ret_ty != ty::Int(int::I32) {
                    return Err(ast_error::IncorrectType {
                        expected: ty::Int(int::I32),
                        found: main.ret_ty.clone(),
                        compiler: fl!(),
                    });
                }
                if main.args_ty.len() != 0 {
                    return Err(ast_error::IncorrectNumberOfArguments {
                        passed: 0,
                        expected: main.args_ty.len(),
                        function: "main".to_owned(),
                    });
                }
                let mut engine: LLVMExecutionEngineRef = std::mem::uninitialized();
                error = std::ptr::null_mut();
                LLVMLinkInMCJIT();
                LLVM_InitializeNativeTarget();
                LLVM_InitializeNativeAsmPrinter();
                if LLVMCreateJITCompilerForModule(&mut engine, self.module.raw,
                        0, &mut error) != 0 {
                    writeln!(std::io::stderr(), "failed to create execution engine: {:?}",
                        CStr::from_ptr(error)).unwrap();
                    LLVMDisposeMessage(error);
                    std::process::exit(-1);
                }

                let res = LLVMRunFunction(engine, main.raw, 0, std::ptr::null_mut());
                println!("{}", LLVMGenericValueToInt(res, true as LLVMBool) as i32);

                LLVMDisposeGenericValue(res);
                LLVMDisposeExecutionEngine(engine);
            } else {
                return Err(ast_error::FunctionDoesntExist("main".to_owned()));
            }
        }

        Ok(())
    }

    fn call(&self, ty: ty, callee: &str, builder: LLVMBuilderRef, args: Vec<value>)
            -> Result<value, ast_error> {
        match self.functions.get(callee) {
            Some(f) => {
                if f.args.len() != args.len() {
                    Err(ast_error::IncorrectNumberOfArguments {
                        expected: f.args.len(),
                        passed: args.len(),
                        function: callee.to_owned(),
                    })
                } else if f.ret_ty != ty && ty != ty::Generic {
                    Err(ast_error::IncorrectType {
                        expected: ty,
                        found: f.ret_ty.clone(),
                        compiler: fl!()
                    })
                } else {
                    unsafe {
                        let res = LLVMBuildCall(builder, f.raw,
                            args.iter().map(|v| v.raw).collect::<Vec<_>>().as_mut_ptr(),
                            args.len() as u32, cstr!(""));
                        Ok(value {
                            raw: res,
                            ty: f.ret_ty.clone(),
                        })
                    }
                }
            },
            None => {
                Err(ast_error::FunctionDoesntExist(callee.to_owned()))
            }
        }
    }

    fn fn_params(&self, name: &str) -> Result<&[ty], ast_error> {
        match self.functions.get(name) {
            Some(f) => Ok(&f.args_ty),
            None => Err(ast_error::FunctionDoesntExist(name.to_owned())),
        }
    }
}
struct module {
    raw: LLVMModuleRef,
}

impl module {
    fn new(name: &str) -> module {
        unsafe {
            let raw = LLVMModuleCreateWithName(CString::new(name)
                .expect("passed a string with a nul to module::new").as_ptr());

            module {
                raw: raw
            }
        }
    }
}

#[derive(Clone, Debug)]
struct value {
    ty: ty,
    raw: LLVMValueRef,
}

impl value {
    fn int_literal(ty: ty, val: u64) -> Result<value, ast_error> {
        match ty {
            ty::Int(_) => {
                let llvm_ty = ty.to_llvm();
                Ok(value {
                    ty: ty,
                    raw: unsafe { LLVMConstInt(llvm_ty, val, false as LLVMBool) },
                })
            }
            ty::Generic => {
                let ty = ty::Int(int::I32); // TODO(ubsan): real int generics
                let llvm_ty = ty.to_llvm();
                Ok(value {
                    ty: ty,
                    raw: unsafe { LLVMConstInt(llvm_ty, val, false as LLVMBool) },
                })
            }
            ty => {
                Err(ast_error::IncorrectType {
                    expected: ty,
                    found: ty::Generic,
                    compiler: fl!(),
                })
            }
        }
    }

    fn bool_literal(ty: ty, val: bool) -> Result<value, ast_error> {
        match ty {
            ty::Bool | ty::Generic => {
                let ty = ty::Bool;
                let llvm_ty = ty.to_llvm();
                Ok(value {
                    ty: ty,
                    raw: unsafe { LLVMConstInt(llvm_ty, val as u64, false as LLVMBool) },
                })
            }
            ty => {
                Err(ast_error::IncorrectType {
                    expected: ty,
                    found: ty::Generic,
                    compiler: fl!(),
                })
            }
        }
    }

    fn parameter(ty: ty, function: &function, name: &str) -> Result<value, ast_error> {
        if let Some(&(i, ref param_ty)) = function.args.get(name) {
            if param_ty == &ty || ty == ty::Generic {
                Ok(value {
                    ty: param_ty.clone(),
                    raw: unsafe { LLVMGetParam(function.raw, i as u32) },
                })
            } else {
                Err(ast_error::IncorrectType {
                    expected: ty,
                    found: param_ty.clone(),
                    compiler: fl!(),
                })
            }
        } else {
            Err(ast_error::UndefinedVariableName {
                name: name.to_owned(),
                function: function.dbg_name.clone(),
            })
        }
    }

    fn binop(ty: ty, op: &operand, lhs: value, rhs: value, builder: LLVMBuilderRef)
            -> Result<value, ast_error> {
        match *op {
            operand::Mul => lhs.mul(rhs, builder, ty),
            operand::Div => lhs.div(rhs, builder, ty),
            operand::Rem => lhs.rem(rhs, builder, ty),
            operand::Plus => lhs.add(rhs, builder, ty),
            operand::Minus => lhs.sub(rhs, builder, ty),

            operand::Shl => lhs.shl(rhs, builder, ty),
            operand::Shr => lhs.shr(rhs, builder, ty),

            operand::And => lhs.and(rhs, builder, ty),
            operand::Xor => lhs.xor(rhs, builder, ty),
            operand::Or => lhs.or(rhs, builder, ty),

            operand::EqualsEquals => lhs.eq(rhs, builder, ty),
            operand::NotEquals => lhs.neq(rhs, builder, ty),
            operand::LessThan => lhs.le(rhs, builder, ty),
            operand::LessThanEquals => lhs.lte(rhs, builder, ty),
            operand::GreaterThan => lhs.gt(rhs, builder, ty),
            operand::GreaterThanEquals => lhs.gte(rhs, builder, ty),

            operand::AndAnd => unreachable!("should be an if statement"),
            operand::OrOr => unreachable!("should be an if statement"),
            operand::Not => unreachable!("Not (`!`) is not a binop"),
        }
    }

    fn mul(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && self.ty == ty {
            if let ty::Int(_) = self.ty {
                return Ok(value {
                    raw: unsafe { LLVMBuildMul(builder, self.raw, rhs.raw, cstr!("")) },
                    ty: self.ty,
                });
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::Mul,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn div(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && self.ty == ty {
            if let ty::Int(_) = self.ty {
                return Ok(value {
                    raw: unsafe { LLVMBuildSDiv(builder, self.raw, rhs.raw, cstr!("")) },
                    ty: self.ty,
                });
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::Div,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn rem(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && self.ty == ty {
            if let ty::Int(_) = self.ty {
                return Ok(value {
                    raw: unsafe { LLVMBuildSRem(builder, self.raw, rhs.raw, cstr!("")) },
                    ty: self.ty,
                });
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::Rem,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn add(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && self.ty == ty {
            if let ty::Int(_) = self.ty {
                return Ok(value {
                    raw: unsafe { LLVMBuildAdd(builder, self.raw, rhs.raw, cstr!("")) },
                    ty: self.ty,
                });
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::Plus,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn sub(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && self.ty == ty {
            if let ty::Int(_) = self.ty {
                return Ok(value {
                    raw: unsafe { LLVMBuildSub(builder, self.raw, rhs.raw, cstr!("")) },
                    ty: self.ty,
                });
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::Minus,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn shl(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == ty {
            if let ty::Int(ref l_t) = self.ty {
                unsafe {
                    let shift_mask = l_t.shift_mask();
                    let safe_rhs = LLVMBuildAnd(builder, rhs.raw,
                        LLVMConstInt(rhs.ty.to_llvm(), shift_mask, false as LLVMBool),
                        cstr!(""));
                    return Ok(value {
                        raw: LLVMBuildShl(builder, self.raw, safe_rhs, cstr!("")),
                        ty: ty,
                    });
                }
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::Shl,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn shr(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == ty {
            if let (&ty::Int(ref l_t), &ty::Int(_)) = (&self.ty, &rhs.ty) {
                unsafe {
                    let shift_mask = l_t.shift_mask();
                    let safe_rhs = LLVMBuildAnd(builder, rhs.raw,
                        LLVMConstInt(rhs.ty.to_llvm(), shift_mask, false as LLVMBool),
                        cstr!(""));
                    return Ok(value {
                        raw: LLVMBuildAShr(builder, self.raw, safe_rhs, cstr!("")),
                        ty: ty,
                    });
                }
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::Shr,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn and(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && self.ty == ty {
            match self.ty {
                ty::Int(_) | ty::Bool =>
                    return Ok(value {
                        raw: unsafe { LLVMBuildAnd(builder, self.raw, rhs.raw, cstr!("")) },
                        ty: self.ty,
                    }),
                _ => {}
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::And,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn xor(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && self.ty == ty {
            match self.ty {
                ty::Int(_) | ty::Bool =>
                    return Ok(value {
                        raw: unsafe { LLVMBuildXor(builder, self.raw, rhs.raw, cstr!("")) },
                        ty: self.ty,
                    }),
                _ => {}
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::Xor,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn or(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && self.ty == ty {
            match self.ty {
                ty::Int(_) | ty::Bool =>
                    return Ok(value {
                        raw: unsafe { LLVMBuildOr(builder, self.raw, rhs.raw, cstr!("")) },
                        ty: self.ty,
                    }),
                _ => {}
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::Or,
            lhs: self.ty, rhs: rhs.ty,
        })
    }

    fn eq(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && ty == ty::Bool || ty == ty::Generic {
            match self.ty {
                ty::Int(_) | ty::Bool =>
                    return Ok(value {
                        raw: unsafe { LLVMBuildICmp(builder, LLVMIntEQ, self.raw, rhs.raw, cstr!("")) },
                        ty: ty::Bool,
                    }),
                _ => {}
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::EqualsEquals,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn neq(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && ty == ty::Bool {
            match self.ty {
                ty::Int(_) | ty::Bool =>
                    return Ok(value {
                        raw: unsafe { LLVMBuildICmp(builder, LLVMIntNE, self.raw, rhs.raw, cstr!("")) },
                        ty: ty::Bool,
                    }),
                _ => {}
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::NotEquals,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn le(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && ty == ty::Bool {
            if let ty::Int(_) = self.ty {
                return Ok(value {
                    raw: unsafe { LLVMBuildICmp(builder, LLVMIntSLT, self.raw, rhs.raw, cstr!("")) },
                    ty: ty::Bool,
                });
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::LessThan,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn lte(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && ty == ty::Bool {
            if let ty::Int(_) = self.ty {
                return Ok(value {
                    raw: unsafe { LLVMBuildICmp(builder, LLVMIntSLE, self.raw, rhs.raw, cstr!("")) },
                    ty: ty::Bool,
                });
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::LessThanEquals,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn gt(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && ty == ty::Bool {
            if let ty::Int(_) = self.ty {
                return Ok(value {
                    raw: unsafe { LLVMBuildICmp(builder, LLVMIntSGT, self.raw, rhs.raw, cstr!("")) },
                    ty: ty::Bool,
                });
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::GreaterThanEquals,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn gte(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && ty == ty::Bool {
            if let ty::Int(_) = self.ty {
                return Ok(value {
                    raw: unsafe { LLVMBuildICmp(builder, LLVMIntSGE, self.raw, rhs.raw, cstr!("")) },
                    ty: ty::Bool,
                });
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::GreaterThanEquals,
            lhs: self.ty, rhs: rhs.ty,
        })
    }


    fn neg(self, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == ty {
            if let ty::Int(_) = self.ty {
                return Ok(value {
                    raw: unsafe { LLVMBuildNeg(builder, self.raw, cstr!("")) },
                    ty: self.ty,
                });
            }
        }
        Err(ast_error::UnopUnsupported {
            op: operand::Minus,
            inner: self.ty,
        })
    }
    fn not(self, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == ty {
            match self.ty {
                ty::Int(_) | ty::Bool => {
                    return Ok(value {
                        raw: unsafe { LLVMBuildNeg(builder, self.raw, cstr!("")) },
                        ty: self.ty,
                    });
                }
                _ => {}
            }
        }
        Err(ast_error::UnopUnsupported {
            op: operand::Not,
            inner: self.ty,
        })
    }
}
