#![allow(non_camel_case_types, dead_code)]

extern crate llvm_sys;

macro_rules! cstr {
    ($s:expr) => (
        concat!($s, "\0").as_ptr() as *const i8
    )
}

macro_rules! fl {
    () => ((file!(), line!()))
}

mod parse;
mod trans;
mod ty;
use parse::lexer;
use trans::ast;

fn main() {
    use std::io::Read;
    let mut file = Vec::new();
    std::fs::File::open("test.pnk").expect("test.rmm")
        .read_to_end(&mut file).unwrap();
    let file = String::from_utf8(file).unwrap();
    let lexer = lexer::new(&file);

    let ast = match ast::create(lexer) {
        Ok(ast) => ast,
        Err(e) => panic!("\n{:#?}", e),
    };

    ast.build().unwrap();
}
