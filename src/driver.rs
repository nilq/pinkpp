extern crate argparse;
extern crate typed_arena;

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

// TODO(ubsan): unify parameter ordering

mod parse;
mod ast;
mod ty;
mod mir;
use parse::Lexer;
use ast::Ast;

fn main() {
    use std::io::Read;

    let mut name = "".to_owned();
    let mut output = None;
    let mut print_mir = false;
    let mut print_asm = false;
    let mut opt = false;
    {
        use argparse::{ArgumentParser, Store, StoreOption, StoreTrue};

        let mut ap = ArgumentParser::new();
        ap.set_description("The pinkc compiler for the pink language.\n\
            Written in Rust.");
        ap.refer(&mut name).required().add_argument("name", Store,
            "The file to compile");
        ap.refer(&mut output).add_option(&["-o", "--output"], StoreOption,
            "Where to put the compiled file");
        ap.refer(&mut print_mir).add_option(&["--print-mir"], StoreTrue,
            "Pass if you would like to print the generated MIR");
        ap.refer(&mut print_asm).add_option(&["--print-asm"], StoreTrue,
            "Pass if you would like to print the generated assembly");
        ap.refer(&mut opt).add_option(&["--opt", "-O"], StoreTrue,
            "Pass if you would like to optimize the generated assembly");

        ap.parse_args_or_exit();
    }

    let mut file = Vec::new();
    std::fs::File::open(&name).expect(&name)
        .read_to_end(&mut file).unwrap();
    let file = String::from_utf8(file).unwrap();
    let lexer = Lexer::new(&file);
    let tyctxt = ty::TypeContext::new();

    let ast = match Ast::create(lexer, &tyctxt) {
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

    // TODO(ubsan): write code for other platforms
    mir.build(&(output.unwrap_or(get_output_from_name(&name))), print_asm, opt)
        .unwrap()
}

// TODO(ubsan): take off the ".pnk" of the input file
fn get_output_from_name(name: &str) -> String {
    format!("{}.s", name)
}
