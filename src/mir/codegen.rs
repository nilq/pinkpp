use std;
use super::{Value, ValueKind, ValueLeaf, Const};

fn name_mangle(name: &str) -> String {
    format!("_{}", name)
}

#[derive(Debug)]
pub struct Generator {
    code: String,
}

impl Generator {
    pub fn new() -> Generator {
        Generator {
            code: ".intel_syntax".to_owned(),
        }
    }

    pub fn add_global(&mut self, name: &str) {
        let name = name_mangle(name);
        self.code.push_str("\n.globl ");
        self.code.push_str(&name);
    }

    pub fn start_function(&mut self, name: &str) {
        let name = name_mangle(name);
        self.code.push('\n');
        self.code.push_str(&name);
        self.code.push(':');
        self.code.push_str(r"
    push rbp
    mov rbp, rsp")

    }

    pub fn write_to_ret(&mut self, value: Value) {
        match value.0 {
            ValueKind::Leaf(leaf) => {
                match leaf {
                    ValueLeaf::Const(Const::Int { value, .. }) => {
                        self.code.push_str(&format!("\n    mov rax, {}",
                            value))
                    },
                    _ => unimplemented!(),
                }
            }
            _ => unimplemented!(),
        }

    }

    pub fn build_ret(&mut self) {
        self.code.push_str(
r"
    mov rsp, rbp
    pop rbp
    ret"
        )
    }

    pub fn add_block(&mut self, name: &str) {
        self.code.push('\n');
        self.code.push_str(name);
        self.code.push(':');
    }

    pub fn build_goto(&mut self, name: &str) {
        self.code.push_str(&format!("\n    jmp {}", name));
    }

    pub fn print(&self) {
        println!("{}", self.code);
    }

    pub fn write_to_file<P>(&self, path: P) -> Result<(), std::io::Error>
            where P: AsRef<std::path::Path> {
        use std::io::Write;
        let mut file = try!(std::fs::File::create(path));
        try!(file.write_all(self.code.as_bytes()));
        Ok(())
    }
}
