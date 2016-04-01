use super::{Mir, Function, Terminator, Statement, Lvalue, Literal,
    Value, ValueKind, Local};
use std::fmt::{Debug, Display, Formatter, Error};

impl<'t> Display for Function<'t> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        for var in self.locals.iter() {
            try!(writeln!(f, "  let {}: {};", var.0, var.1));
        }
        for (i, block) in self.blocks.iter().enumerate() {
            try!(writeln!(f, "  bb{}: {{", i));
            for stmt in &block.statements {
                try!(writeln!(f, "    {};", stmt.display(self)));
            }
            try!(writeln!(f, "    {};", block.terminator.display(self)));
            try!(writeln!(f, "  }}"));
        }
        Ok(())
    }
}

// TODO(ubsan): could probably do this without the allocations of String
impl Statement {
    fn display(&self, func: &Function) -> String {
        format!("{} = {}", (self.0).display(func), (self.1).display(func))
    }
}

impl Lvalue {
    fn display(&self, func: &Function) -> String {
        match *self {
            Lvalue::Return => "return".to_owned(),
            Lvalue::Local(ref loc) => loc.display(func),
            Lvalue::Deref(ref ptr) =>
                "*".to_owned() + &ptr.display(func)
        }
    }
}

impl Terminator {
    fn display(&self, func: &Function) -> String {
        match *self {
            Terminator::Goto(ref b) => format!("goto -> bb{}", b.0),
            Terminator::Return => "return".to_owned(),
            Terminator::If {
                ref cond,
                ref then_blk,
                ref else_blk,
            } => format!("if({}) -> [true: bb{}, false: bb{}]",
                cond.display(func), then_blk.0, else_blk.0),
        }
    }
}

impl Local {
    fn display(&self, func: &Function) -> String {
        func.get_local_name(*self).to_owned()
    }
}

impl Value {
    fn display(&self, func: &Function) -> String {
        match self.0 {
            ValueKind::Literal(ref lit) => format!("lit {}", lit.display(func)),
            ValueKind::Parameter(ref par) => format!("par{}", par.0),
            ValueKind::Lvalue(ref lv) => format!("{}", lv.display(func)),
            ValueKind::Pos(ref inner) => format!("Pos({})",
                inner.display(func)),
            ValueKind::Neg(ref inner) => format!("Neg({})",
                inner.display(func)),
            ValueKind::Not(ref inner) => format!("Not({})",
                inner.display(func)),
            ValueKind::Ref(ref inner) => format!("&{}",
                inner.display(func)),
            ValueKind::Add(ref lhs, ref rhs)
                => format!("Add({}, {})", lhs.display(func), rhs.display(func)),
            ValueKind::Sub(ref lhs, ref rhs)
                => format!("Sub({}, {})", lhs.display(func), rhs.display(func)),
            ValueKind::Mul(ref lhs, ref rhs)
                => format!("Mul({}, {})", lhs.display(func), rhs.display(func)),
            ValueKind::Div(ref lhs, ref rhs)
                => format!("Div({}, {})", lhs.display(func), rhs.display(func)),
            ValueKind::Rem(ref lhs, ref rhs)
                => format!("Rem({}, {})", lhs.display(func), rhs.display(func)),
            ValueKind::And(ref lhs, ref rhs)
                => format!("And({}, {})", lhs.display(func), rhs.display(func)),
            ValueKind::Xor(ref lhs, ref rhs)
                => format!("And({}, {})", lhs.display(func), rhs.display(func)),
            ValueKind::Or(ref lhs, ref rhs)
                => format!("And({}, {})", lhs.display(func), rhs.display(func)),
            ValueKind::Shl(ref lhs, ref rhs)
                => format!("Shl({}, {})", lhs.display(func), rhs.display(func)),
            ValueKind::Shr(ref lhs, ref rhs)
                => format!("Shr({}, {})", lhs.display(func), rhs.display(func)),

            ValueKind::Eq(ref lhs, ref rhs)
                => format!("Eq({}, {})", lhs.display(func), rhs.display(func)),
            ValueKind::Neq(ref lhs, ref rhs)
                => format!("Neq({}, {})", lhs.display(func), rhs.display(func)),
            ValueKind::Lt(ref lhs, ref rhs)
                => format!("Lt({}, {})", lhs.display(func), rhs.display(func)),
            ValueKind::Lte(ref lhs, ref rhs)
                => format!("Lte({}, {})", lhs.display(func), rhs.display(func)),
            ValueKind::Gt(ref lhs, ref rhs)
                => format!("Gt({}, {})", lhs.display(func), rhs.display(func)),
            ValueKind::Gte(ref lhs, ref rhs)
                => format!("Gte({}, {})", lhs.display(func), rhs.display(func)),

            ValueKind::Call {
                ref callee,
                ref args,
            } => {
                let mut s = format!("{}(", callee);
                if args.len() != 0 {
                    for arg in &args[..args.len() - 1] {
                        s.push_str(&arg.display(func));
                    }
                    s.push_str(&args[args.len() - 1].display(func));
                }
                s.push(')');
                s
            }
        }
    }
}

impl Literal {
    fn display(&self, func: &Function) -> String {
        match *self {
            Literal::Int {
                signed,
                value,
                ..
            } => {
                if signed {
                    format!("{}", value as i64)
                } else {
                    format!("{}", value as u64)
                }
            }
            Literal::Bool(ref value) => format!("{}", value),
            Literal::Tuple(ref v) => {
                if v.len() == 0 {
                    "()".to_owned()
                } else {
                    let mut s = "(".to_owned();
                    for el in &v[..v.len() - 1] {
                        s.push_str(&el.display(func));
                        s.push_str(", ");
                    }
                    s.push_str(&v[v.len() - 1].display(func));
                    s.push(')');
                    s
                }
            }
        }
    }
}


impl<'t> Display for Mir<'t> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
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
            try!(write!(f, "{}", function));
            try!(writeln!(f, "}}\n"));
        }
        Ok(())
    }
}
impl<'t> Debug for Mir<'t> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        write!(f, "{}", self)
    }
}
