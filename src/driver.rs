#![deny(warnings)]

extern crate llvm_sys;

macro_rules! cstr {
    ($s:expr) => (
        concat!($s, "\0").as_ptr() as *const i8
    )
}

macro_rules! fl {
    () => ((file!(), line!()));
    (line:$expr) => ((file!(), line));
}

enum Either<L, R> {
    Left(L),
    Right(R),
}

mod parse;
mod ast;
mod ty;
mod mir;
use parse::Lexer;
use ast::Ast;

fn main() {
    use std::io::Read;
    let mut file = Vec::new();
    std::fs::File::open("test.pnk").expect("test.pnk")
        .read_to_end(&mut file).unwrap();
    let file = String::from_utf8(file).unwrap();
    let lexer = Lexer::new(&file);

    let ast = match Ast::create(lexer) {
        Ok(ast) => ast,
        Err(e) => panic!("\n{:#?}", e),
    };
    let mir = match ast.typeck() {
        Ok(mir) => mir,
        Err(e) => panic!("\n{:#?}", e),
    };
    println!("{}", mir);

    mir.build()
}
