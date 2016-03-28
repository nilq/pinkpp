use super::{Mir, Function, Terminator, Statement, Lvalue, Const,
    Value, ValueLeaf, ValueKind};
use ty::TypeVariant;
use std::fmt::{Debug, Display, Formatter, Error};

impl<'t> Display for Function<'t> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        for (i, var) in self.locals.iter().enumerate() {
            try!(writeln!(f, "  let var{}: {};", i, var));
        }
        for (i, tmp) in self.temporaries.iter().enumerate() {
            try!(writeln!(f, "  let tmp{}: {};", i, tmp));
        }
        for (i, block) in self.blocks.iter().enumerate() {
            try!(writeln!(f, "  bb{}: {{", i));
            for stmt in &block.statements {
                try!(writeln!(f, "    {};", stmt));
            }
            try!(writeln!(f, "    {};", block.terminator));
            try!(writeln!(f, "  }}"));
        }
        Ok(())
    }
}

impl<'t> Display for Terminator<'t> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        match *self {
            Terminator::Goto(ref b) => write!(f, "goto -> bb{}", b.0),
            Terminator::Return => write!(f, "return"),
            Terminator::If {
                ref cond,
                ref then_blk,
                ref else_blk,
            } => write!(f, "if({}) -> [true: bb{}, false: bb{}]", cond,
                then_blk.0, else_blk.0),
        }
    }
}

impl<'t> Display for Statement<'t> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        write!(f, "{} = {}", self.0, self.1)
    }
}

impl<'t> Display for Lvalue<'t> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        match *self {
            Lvalue::Return => write!(f, "return"),
            Lvalue::Temporary(ref tmp) => write!(f, "tmp{}", tmp.0),
            Lvalue::Variable(ref var) => write!(f, "var{}", var.0),
            Lvalue::Deref(ref ptr) => write!(f, "(*{})", ptr),
        }
    }
}

impl<'t> Display for Const<'t> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        match *self {
            Const::Int {
                ref ty,
                ref value,
            } => {
                match *ty.0 {
                    TypeVariant::SInt(_) => write!(f, "{}", *value as i64),
                    TypeVariant::UInt(_) => write!(f, "{}", *value as u64),
                    _ => panic!("Non-integer int"),
                }
            }
            Const::Bool(ref value) => write!(f, "{}", value),
            Const::Unit => write!(f, "()"),
        }
    }
}

impl<'t> Display for ValueLeaf<'t> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        match *self {
            ValueLeaf::Const(ref inner) => write!(f, "const {}", inner),
            ValueLeaf::Temporary(ref tmp) => write!(f, "tmp{}", tmp.0),
            ValueLeaf::Parameter(ref par) => write!(f, "arg{}", par.0),
            ValueLeaf::Variable(ref var) => write!(f, "var{}", var.0),
        }
    }
}

impl<'t> Display for Value<'t> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        match self.0 {
            ValueKind::Leaf(ref v) => write!(f, "{}", v),
            ValueKind::Pos(ref inner) => write!(f, "Pos({})", inner),
            ValueKind::Neg(ref inner) => write!(f, "Neg({})", inner),
            ValueKind::Not(ref inner) => write!(f, "Not({})", inner),
            ValueKind::Ref(ref inner) => write!(f, "&{}", inner),
            ValueKind::Deref(ref inner) => write!(f, "*{}", inner),
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
