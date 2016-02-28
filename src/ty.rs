use std;
use llvm_sys::prelude::*;
use llvm_sys::core::*;

use parse::{parser_error};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ty {
    SInt(int),
    UInt(int),
    Bool,
    Unit,
    Diverging,
    Generic,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum int {
    I32,
}

impl ty {
    pub fn from_str(s: &str, line: u32) -> Result<ty, parser_error> {
        match s {
            "s32" => Ok(ty::SInt(int::I32)),
            "u32" => Ok(ty::UInt(int::I32)),
            "bool" => Ok(ty::Bool),
            "()" => Ok(ty::Unit),
            "!" => Ok(ty::Diverging),
            s => Err(parser_error::UnknownType {
                found: s.to_owned(),
                line: line,
                compiler: fl!(),
            }),
        }
    }

    // TODO(ubsan): we need to convert zero sized return types into void
    pub fn to_llvm(&self) -> LLVMTypeRef {
        unsafe {
            match *self {
                ty::SInt(ref size) | ty::UInt(ref size) => LLVMIntType(size.size()),
                ty::Bool => LLVMInt1Type(),
                ty::Unit => LLVMStructType(std::ptr::null_mut(), 0, false as LLVMBool),
                ty::Diverging => unreachable!("Diverging is not a real type"),
                ty::Generic => unreachable!("Generic is not a real type"),
            }
        }
    }

    pub fn to_llvm_ret(&self) -> LLVMTypeRef {
        unsafe {
            match *self {
                ty::SInt(ref size) | ty::UInt(ref size) => LLVMIntType(size.size()),
                ty::Bool => LLVMInt1Type(),
                ty::Unit => LLVMVoidType(),
                ty::Diverging => LLVMVoidType(),
                ty::Generic => unreachable!("Generic is not a real type"),
            }
        }
    }
}

impl int {
    pub fn shift_mask(&self) -> u64 {
        match *self {
            // int::I8 => (1 << 3) - 1,
            // int::I16 => (1 << 4) - 1,
            int::I32 => (1 << 5) - 1,
            // int::I64 => (1 << 6) - 1,
        }
    }

    pub fn size(&self) -> u32 {
        match *self {
            // int::I8 => 8,
            // int::I16 => 16,
            int::I32 => 32,
            // int::I64 => 64,
        }
    }
}
