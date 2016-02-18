use std;
use std::collections::HashMap;
use std::ffi::{ CString, CStr };
use parse::{ lexer, operand, parser, parser_error };

use llvm_sys::LLVMIntPredicate::*;
use llvm_sys::execution_engine::*;
use llvm_sys::target::*;
use llvm_sys::prelude::*;
use llvm_sys::analysis::*;
use llvm_sys::analysis::LLVMVerifierFailureAction::*;
use llvm_sys::core::*;

// TODO(ubsan): start taking &mut self?

fn translate_binop(op: &operand, lhs: LLVMValueRef, rhs: LLVMValueRef, builder: LLVMBuilderRef)
        -> LLVMValueRef {
    unsafe {
        match *op {
            operand::Mul => LLVMBuildMul(builder, lhs, rhs, cstr!("")),
            operand::Div => LLVMBuildSDiv(builder, lhs, rhs, cstr!("")),
            operand::Rem => LLVMBuildSRem(builder, lhs, rhs, cstr!("")),
            operand::Plus => LLVMBuildAdd(builder, lhs, rhs, cstr!("")),
            operand::Minus => LLVMBuildSub(builder, lhs, rhs, cstr!("")),

            // TODO(ubsan): make shr and shl defined (& by number of bits)
            operand::Shl => LLVMBuildShl(builder, lhs, rhs, cstr!("")),
            operand::Shr => LLVMBuildSRem(builder, lhs, rhs, cstr!("")),

            operand::BitAnd => LLVMBuildAnd(builder, lhs, rhs, cstr!("")),
            operand::BitXor => LLVMBuildXor(builder, lhs, rhs, cstr!("")),
            operand::BitOr => LLVMBuildOr(builder, lhs, rhs, cstr!("")),

            operand::EqualsEquals => {
                let bool_res = LLVMBuildICmp(builder, LLVMIntEQ, lhs, rhs, cstr!(""));
                LLVMBuildZExt(builder, bool_res, LLVMInt32Type(), cstr!(""))
            }
            operand::NotEquals => {
                let bool_res = LLVMBuildICmp(builder, LLVMIntNE, lhs, rhs, cstr!(""));
                LLVMBuildZExt(builder, bool_res, LLVMInt32Type(), cstr!(""))
            }
            operand::LessThan => {
                let bool_res = LLVMBuildICmp(builder, LLVMIntSLT, lhs, rhs, cstr!(""));
                LLVMBuildZExt(builder, bool_res, LLVMInt32Type(), cstr!(""))
            }
            operand::LessThanEquals => {
                let bool_res = LLVMBuildICmp(builder, LLVMIntSLE, lhs, rhs, cstr!(""));
                LLVMBuildZExt(builder, bool_res, LLVMInt32Type(), cstr!(""))
            }
            operand::GreaterThan =>  {
                let bool_res = LLVMBuildICmp(builder, LLVMIntSGT, lhs, rhs, cstr!(""));
                LLVMBuildZExt(builder, bool_res, LLVMInt32Type(), cstr!(""))
            }
            operand::GreaterThanEquals =>  {
                let bool_res = LLVMBuildICmp(builder, LLVMIntSGE, lhs, rhs, cstr!(""));
                LLVMBuildZExt(builder, bool_res, LLVMInt32Type(), cstr!(""))
            }
            operand::AndAnd => panic!("should be an if statement"),
            operand::OrOr => panic!("should be an if statement"),
        }
    }
}

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
    Literal(u32),
}

impl std::fmt::Display for expr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match *self {
            expr::Call {
                ref name,
                ref args,
            } => {
                try!(write!(f, "{}(", name));
                if args.len() > 0 {
                    for arg in &args[..args.len() - 1] {
                        try!(write!(f, "{}, ", arg));
                    }
                    write!(f, "{})", args[args.len() - 1])
                } else {
                    write!(f, ")")
                }
            }
            expr::If {
                ref condition,
                ref then_value,
                ref else_value,
            } => {
                write!(f, "if {} {{ {} }} else {{ {} }}",
                       condition, then_value, else_value)
            }
            expr::Binop {
                ref op,
                ref lhs,
                ref rhs,
            } => {
                write!(f, "({} {} {})", lhs, op, rhs)
            }
            expr::Plus(ref inner) => { write!(f, "+{}", inner) }
            expr::Minus(ref inner) => { write!(f, "-{}", inner) }
            expr::Not(ref inner) => { write!(f, "!{}", inner) }
            expr::Variable(ref name) => {
                write!(f, "{}", name)
            }
            expr::Literal(ref lit) => {
                write!(f, "{}", lit)
            }
        }
    }
}

impl expr {
    fn translate(self, function: &llfunction, builder: LLVMBuilderRef, ast: &ast)
            -> Result<LLVMValueRef, ast_error> {
        unsafe {
            let ret_ty = LLVMInt32Type();
            match self {
                expr::Literal(i) => {
                    Ok(LLVMConstInt(ret_ty, i as u64, false as LLVMBool))
                }
                expr::Variable(ref name) => {
                    // TODO(ubsan): local variables
                    /*if let Some(i) = locals_hm.get(name) {
                        Ok(locals_values[*i])
                    } else*/
                    if let Some(i) = function.args.get(name) {
                        Ok(LLVMGetParam(function.raw, *i as u32))
                    } else {
                        Err(ast_error::UndefinedVariableName {
                            name: name.clone(),
                            allowed: function.args.keys().map(|s| s.to_owned()).collect(),
                        })
                    }
                }
                expr::Binop {
                    op: operand::OrOr,
                    lhs,
                    rhs,
                } => {
                    expr::If {
                        condition: lhs,
                        then_value: Box::new(expr::Literal(1)),
                        else_value: rhs,
                    }.translate(function, builder, ast)
                }
                expr::Binop {
                    op: operand::AndAnd,
                    lhs,
                    rhs,
                } => {
                    expr::If {
                        condition: Box::new(expr::Not(lhs)),
                        then_value: Box::new(expr::Literal(1)),
                        else_value: rhs,
                    }.translate(function, builder, ast)
                }
                expr::Binop {
                    op,
                    lhs,
                    rhs,
                } => {
                    let lhs = try!(lhs.translate(function, builder, ast));
                    let rhs = try!(rhs.translate(function, builder, ast));
                    Ok(translate_binop(&op, lhs, rhs, builder))
                }
                expr::Plus(inner) => {
                    inner.translate(function, builder, ast)
                }
                expr::Minus(inner) => {
                    inner.translate(function, builder, ast)
                        .map(|v| LLVMBuildNeg(builder, v, cstr!("")))
                }
                expr::Not(inner) => {
                    let val = try!(inner.translate(function, builder, ast));
                    let bool_res = LLVMBuildICmp(builder, LLVMIntEQ, val,
                        LLVMConstInt(LLVMInt32Type(), 0, false as LLVMBool), cstr!(""));
                    Ok(LLVMBuildZExt(builder, bool_res, LLVMInt32Type(), cstr!("")))
                }
                expr::If {
                    condition,
                    then_value,
                    else_value,
                } => {
                    let then_blk = LLVMAppendBasicBlock(function.raw, cstr!("then"));
                    let else_blk = LLVMAppendBasicBlock(function.raw, cstr!("else"));
                    let join_blk = LLVMAppendBasicBlock(function.raw, cstr!("join"));

                    let cond = try!(condition.translate(function, builder, ast));
                    let cond_bool = LLVMBuildICmp(builder, LLVMIntNE, cond,
                        LLVMConstInt(LLVMInt32Type(), 0, false as LLVMBool), cstr!(""));
                    LLVMBuildCondBr(builder, cond_bool, then_blk, else_blk);

                    // TODO(ubsan): builder wrapping class
                    LLVMPositionBuilderAtEnd(builder, then_blk);
                    let then_res = try!(then_value.translate(function, builder, ast));
                    let then_end_blk = LLVMGetInsertBlock(builder);
                    LLVMBuildBr(builder, join_blk);

                    LLVMPositionBuilderAtEnd(builder, else_blk);
                    let else_res = try!(else_value.translate(function, builder, ast));
                    let else_end_blk = LLVMGetInsertBlock(builder);
                    LLVMBuildBr(builder, join_blk);

                    LLVMPositionBuilderAtEnd(builder, join_blk);
                    let res = LLVMBuildPhi(builder, LLVMInt32Type(), cstr!(""));
                    let mut phi_vals = [then_res, else_res];
                    let mut preds = [then_end_blk, else_end_blk];
                    LLVMAddIncoming(res, phi_vals.as_mut_ptr(), preds.as_mut_ptr(), 2);

                    Ok(res)
                }
                expr::Call {
                    name,
                    args,
                } => {
                    let mut llvm_args = Vec::new();
                    for arg in args {
                        llvm_args.push(try!(arg.translate(function, builder, ast)));
                    }
                    ast.call(&name, builder, llvm_args)
                }
            }
        }
    }
}

#[derive(Debug)]
pub enum stmt {
    Return(expr),
    Let {
        name: String,
        value: expr,
    },
}

#[derive(Debug)]
pub enum item {
    Function {
        name: String,
        args: Vec<String>,
        body: Vec<stmt>,
    }
}

struct llfunction {
    args: HashMap<String, usize>,
    raw: LLVMValueRef,
}

impl llfunction {
    fn new(name: String, args: Vec<String>, module: LLVMModuleRef)
            -> Result<llfunction, parser_error> {
        let mut args_hashmap = HashMap::new();
        let mut arg_index = 0;
        for arg in args {
            if !args_hashmap.contains_key(&arg) {
                debug_assert!(args_hashmap.insert(arg, arg_index).is_none());
                arg_index += 1;
            } else {
                return Err(parser_error::DuplicatedFunctionArgument {
                    argument: arg,
                    function: name,
                    compiler_line: line!(),
                });
            }
        }

        let raw = unsafe {
            let ret_ty = LLVMInt32Type();
            let mut params_ty = vec![LLVMInt32Type(); args_hashmap.len()];
            let function_ty = LLVMFunctionType(ret_ty, params_ty.as_mut_ptr(),
                params_ty.len() as u32, false as LLVMBool);

            LLVMAddFunction(module, CString::new(name.clone())
                .expect("name should not have a nul in it").as_ptr(), function_ty)
        };

        Ok(llfunction {
            args: args_hashmap,
            raw: raw,
        })
    }

    fn add_body(&self, body: Vec<stmt>, ast: &ast) -> Result<(), ast_error> {
        unsafe {
            let bb = LLVMAppendBasicBlock(self.raw, cstr!("entry"));
            let builder = LLVMCreateBuilder();
            LLVMPositionBuilderAtEnd(builder, bb);

            for st in body {
                match st {
                    stmt::Let {
                        name: ref _name,
                        value: ref _value,
                    } => {
                        unimplemented!()
                    }
                    stmt::Return(expr) => {
                        let tmp = try!(expr.translate(self, builder, ast));
                        LLVMBuildRet(builder, tmp);
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
        allowed: Vec<String>,
    },
    FunctionDoesntExist(String),
    IncorrectReturnType,
}

pub struct ast {
    functions: HashMap<String, llfunction>,
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
                    args,
                    body,
                }) => {
                    functions.insert(name.clone(),
                        try!(llfunction::new(name.clone(), args, module.raw)));
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

    fn call(&self, callee: &str, builder: LLVMBuilderRef, args: Vec<LLVMValueRef>)
            -> Result<LLVMValueRef, ast_error> {
        match self.functions.get(callee) {
            Some(f) => {
                if f.args.len() == args.len() {
                    unsafe {
                        Ok(LLVMBuildCall(builder, f.raw, args.clone().as_mut_ptr(),
                            args.len() as u32, cstr!("")))
                    }
                } else {
                    Err(ast_error::IncorrectNumberOfArguments {
                        expected: f.args.len(),
                        passed: args.len(),
                        function: callee.to_owned(),
                    })
                }
            },
            None => {
                Err(ast_error::FunctionDoesntExist(callee.to_owned()))
            }
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
