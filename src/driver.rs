extern crate libc;
extern crate llvm_sys;
extern crate argparse;

macro_rules! cstr {
    ($s:expr) => (
        concat!($s, "\0").as_ptr() as *const ::libc::c_char
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

    let mut name = "".to_owned();
    let mut print_mir = false;
    let mut print_llir = false;
    {
        use argparse::{ArgumentParser, Store, StoreTrue};

        let mut ap = ArgumentParser::new();
        ap.set_description("The pinkc compiler for the pink language.\n\
            Written in Rust.");
        ap.refer(&mut name).required().add_argument("name", Store,
            "The file to compile");
        ap.refer(&mut print_mir).add_option(&["--print-mir"], StoreTrue,
            "Pass if you would like to print the generated MIR");
        ap.refer(&mut print_llir).add_option(&["--print-llir"], StoreTrue,
            "Pass if you would like to print the generated LLVM IR");

        ap.parse_args_or_exit();
    }

    let mut file = Vec::new();
    std::fs::File::open(&name).expect(&name)
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
    if print_mir {
        println!("{}", mir);
    }

    mir.build(print_llir)
}
