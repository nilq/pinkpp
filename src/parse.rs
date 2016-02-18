use std;
use std::str;
use trans::{ expr, stmt, item };

#[derive(Debug, PartialEq, Eq)]
pub enum token {
    // Item
    KeywordFn,

    // Statement
    KeywordLet,
    KeywordReturn,
    CloseBrace,

    // Expression
    KeywordTrue,
    KeywordFalse,
    KeywordIf,
    KeywordElse,
    BitNot,
    Not,
    Ident(String),
    Integer(u64),

    Operand(operand),

    // Misc
    OpenParen,
    CloseParen,
    OpenBrace,
    Semicolon,
    Comma,
    Equals,
    Eof,
}

impl token {
    pub fn ty(&self) -> token_type {
        match *self {
            token::KeywordFn => token_type::Item,

            token::KeywordLet | token::KeywordReturn | token::CloseBrace
                => token_type::Statement,

            token::KeywordTrue | token::KeywordFalse | token::KeywordIf |
            token::Ident(_) | token::Integer(_) | token::Not | token::BitNot
                => token_type::Expression,

            token::Operand(_) => token_type::Operand,

            token::KeywordElse | token::OpenParen | token::CloseParen |
            token::OpenBrace |  token::Semicolon |
            token::Comma | token::Equals | token::Eof => token_type::Misc,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum operand {
    Mul,
    Div,
    Rem,

    Plus,
    Minus,

    Shl,
    Shr,

    BitAnd,
    BitXor,
    BitOr,

    EqualsEquals,
    NotEquals,
    LessThan,
    LessThanEquals,
    GreaterThan,
    GreaterThanEquals,

    AndAnd,
    OrOr,
}

impl std::fmt::Display for operand {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        let s = match *self {
            operand::Mul => "*",
            operand::Div => "/",
            operand::Rem => "%",
            operand::Plus => "+",
            operand::Minus => "-",
            operand::Shl => "<<",
            operand::Shr => ">>",
            operand::BitAnd => "&",
            operand::BitXor => "^",
            operand::BitOr => "|",
            operand::EqualsEquals => "==",
            operand::NotEquals => "!=",
            operand::LessThan => "<",
            operand::LessThanEquals => "<=",
            operand::GreaterThan => ">",
            operand::GreaterThanEquals => ">=",
            operand::AndAnd => "&&",
            operand::OrOr => "||",
        };
        f.write_str(s)
    }
}

impl operand {
    pub fn precedence(&self) -> u8 {
        match *self {
            operand::Mul | operand::Div | operand::Rem => 9,
            operand::Plus | operand::Minus => 8,
            operand::Shl | operand::Shr => 7,
            operand::BitAnd => 6,
            operand::BitXor => 5,
            operand::BitOr => 4,
            operand::EqualsEquals | operand::NotEquals | operand::LessThan |
            operand::LessThanEquals | operand::GreaterThan | operand::GreaterThanEquals => 3,
            operand::AndAnd => 2,
            operand::OrOr => 1,
        }
    }

    // simply a convenience function
    pub fn expr(&self, lhs: expr, rhs: expr) -> expr {
        expr::Binop {
            op: *self,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs)
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum token_type {
    Item,
    Statement,
    Expression,
    Operand,
    Misc,

    Specific(token),
    AnyOf(Vec<token>),
}

pub struct lexer<'src> {
    src: str::Chars<'src>,
    readahead: Vec<char>,
    line: u32,
}

impl<'src> lexer<'src> {
    pub fn new(src: &str) -> lexer {
        lexer {
            src: src.chars(),
            readahead: Vec::with_capacity(1),
            line: 0,
        }
    }

    fn ident(&mut self, first: char) -> String {
        let mut ret = String::new();
        ret.push(first);
        loop {
            match self.getc() {
                Some(c @ 'a'...'z') | Some(c @ 'A'...'Z') | Some(c @ '0'...'9') | Some(c @ '_') => {
                    ret.push(c)
                }
                Some(c) => {
                    self.ungetc(c);
                    break;
                }
                None => break,
            }
        }

        ret
    }

    fn block_comment(&mut self) -> Result<(), parser_error> {
        loop {
            let c = self.getc();
            if c == Some('*') {
                let c = self.getc();
                if c == Some('/') {
                    return Ok(());
                } else if c == Some('\n') {
                    self.line += 1;
                } else if c == None {
                    return Err(parser_error::UnclosedComment);
                }
            } else if c == Some('/') {
                let c = self.getc();
                if c == Some('*') {
                    try!(self.block_comment())
                } else if c == Some('\n') {
                    self.line += 1;
                } else if c == None {
                    return Err(parser_error::UnclosedComment);
                }
            } else if c == Some('\n') {
                self.line += 1;
            } else if c == None {
                return Err(parser_error::UnclosedComment);
            }
        }
    }

    fn line_comment(&mut self) {
        loop {
            match self.getc() {
                Some('\n') => {
                    self.line += 1;
                    break;
                }
                None => break,
                Some(_) => {}
            }
        }
    }

    fn getc(&mut self) -> Option<char> {
        if let Some(c) = self.readahead.pop() {
            Some(c)
        } else if let Some(c) = self.src.next() {
            Some(c)
        } else {
            None
        }
    }
    fn ungetc(&mut self, c: char) {
        // TODO(ubsan): maybe assert that length == 0?
        self.readahead.push(c)
    }

    fn eat_whitespace(&mut self) -> Option<()> {
        loop {
            let c = match self.getc() {
                Some(c) => c,
                None => return None,
            };
            if !Self::is_whitespace(c) {
                self.ungetc(c);
                break;
            } else if c == '\n' {
                self.line += 1;
            }
        }

        Some(())
    }

    fn is_whitespace(c: char) -> bool {
        c == '\t' || c == '\n' || c == '\r' || c == ' '
    }

    pub fn next_token(&mut self) -> Result<token, parser_error> {
        self.eat_whitespace();
        let first = match self.getc() {
            Some(c) => c,
            None => return Ok(token::Eof),
        };
        match first {
            '(' => Ok(token::OpenParen),
            ')' => Ok(token::CloseParen),
            '{' => Ok(token::OpenBrace),
            '}' => Ok(token::CloseBrace),
            ';' => Ok(token::Semicolon),
            ',' => Ok(token::Comma),
            '~' => Ok(token::BitNot),
            '*' => Ok(token::Operand(operand::Mul)),
            '%' => Ok(token::Operand(operand::Rem)),
            '+' => Ok(token::Operand(operand::Plus)),
            '-' => Ok(token::Operand(operand::Minus)),
            '/' => {
                match self.getc() {
                    Some('*') => {
                        try!(self.block_comment());
                        return self.next_token();
                    }
                    Some('/') => {
                        self.line_comment();
                        return self.next_token();
                    }
                    Some(c) => {
                        self.ungetc(c);
                    }
                    None => { }
                }
                Ok(token::Operand(operand::Div))
            }

            '!' => {
                match self.getc() {
                    Some('=') => {
                        return Ok(token::Operand(operand::NotEquals));
                    }
                    Some(c) => {
                        self.ungetc(c)
                    }
                    None => {}
                }
                Ok(token::Not)
            }
            '<' => {
                match self.getc() {
                    Some('<') => {
                        return Ok(token::Operand(operand::Shl));
                    }
                    Some('=') => {
                        return Ok(token::Operand(operand::LessThanEquals));
                    }
                    Some(c) => {
                        self.ungetc(c)
                    }
                    None => {}
                }
                Ok(token::Operand(operand::LessThan))
            }
            '>' => {
                match self.getc() {
                    Some('>') => {
                        return Ok(token::Operand(operand::Shr));
                    }
                    Some('=') => {
                        return Ok(token::Operand(operand::GreaterThanEquals));
                    }
                    Some(c) => {
                        self.ungetc(c)
                    }
                    None => {}
                }
                Ok(token::Operand(operand::GreaterThan))
            }
            '=' => {
                match self.getc() {
                    Some('=') => {
                        return Ok(token::Operand(operand::EqualsEquals));
                    }
                    Some(c) => {
                        self.ungetc(c)
                    }
                    None => {}
                }
                Ok(token::Equals)
            }
            '&' => {
                match self.getc() {
                    Some('&') => {
                        return Ok(token::Operand(operand::AndAnd));
                    }
                    Some(c) => {
                        self.ungetc(c)
                    }
                    None => {}
                }
                Ok(token::Operand(operand::BitAnd))
            }
            '|' => {
                match self.getc() {
                    Some('|') => {
                        return Ok(token::Operand(operand::OrOr));
                    }
                    Some(c) => {
                        self.ungetc(c)
                    }
                    None => {}
                }
                Ok(token::Operand(operand::BitOr))
            }

            'a'...'z' | 'A'...'Z' | '_' => {
                let ident = self.ident(first);
                match &ident[..] {
                    "fn" => return Ok(token::KeywordFn),
                    "return" => return Ok(token::KeywordReturn),
                    "let" => return Ok(token::KeywordLet),
                    "if" => return Ok(token::KeywordIf),
                    "else" => return Ok(token::KeywordElse),
                    "true" => return Ok(token::KeywordTrue),
                    "false" => return Ok(token::KeywordFalse),
                    _ => {},
                }

                Ok(token::Ident(ident))
            }
            '0'...'9' => {
                let mut string = String::new();
                if first != '-' {
                    string.push(first);
                }
                loop {
                    match self.getc() {
                        Some(c @ '0'...'9') => {
                            string.push(c)
                        }
                        Some(c) => {
                            self.ungetc(c);
                            break;
                        }
                        None => break,
                    }
                }

                let value = string.parse::<u64>()
                    .expect("we pushed something which wasn't 0...9 onto a string");

                Ok(token::Integer(value))
            }

            i => {
                Err(parser_error::InvalidToken {
                    token: i,
                    line: self.line,
                    compiler_line: line!(),
                })
            }
        }
    }
}

#[derive(Debug)]
pub enum parser_error {
    ExpectedEof,

    UnclosedComment,
    InvalidToken {
        token: char,
        line: u32,
        compiler_line: u32,
    },
    DuplicatedFunctionArgument {
        argument: String,
        function: String,
        compiler_line: u32,
    },
    UnexpectedToken {
        found: token,
        expected: token_type,
        line: u32,
        compiler_line: u32,
    },
}

pub struct parser<'src> {
    lexer: lexer<'src>,
    token_buffer: Vec<token>,
}

impl<'src> parser<'src> {
    pub fn new(lexer: lexer<'src>) -> Self {
        parser {
            lexer: lexer,
            token_buffer: Vec::new(),
        }
    }

    #[inline(always)]
    pub fn line(&self) -> u32 {
        self.lexer.line
    }

    fn get_token(&mut self) -> Result<token, parser_error> {
        match self.token_buffer.pop() {
            Some(tok) => Ok(tok),
            None => self.lexer.next_token(),
        }
    }
    fn unget_token(&mut self, token: token) {
        self.token_buffer.push(token)
    }

    pub fn item(&mut self) -> Result<item, parser_error> {
        match try!(self.get_token()) {
            token::KeywordFn => self.function(),
            token::Eof => Err(parser_error::ExpectedEof),
            tok => Err(parser_error::UnexpectedToken {
                found: tok,
                expected: token_type::Item,
                line: self.line(),
                compiler_line: line!(),
            }),
        }
    }

    fn maybe_eat_ty(&mut self, expected: &token_type, _: u32) -> Result<Option<token>, parser_error> {
        let token = try!(self.get_token());
        match *expected {
            token_type::Specific(ref t) => {
                if &token == t {
                    return Ok(Some(token));
                }
            }
            token_type::AnyOf(ref t) => {
                if t.contains(&token) {
                    return Ok(Some(token));
                }
            }
            ref tt => {
                if &token.ty() == tt {
                    return Ok(Some(token));
                }
            }
        }
        self.unget_token(token);
        Ok(None)
    }

    fn eat_ty(&mut self, expected: token_type, line: u32) -> Result<token, parser_error> {
        match self.maybe_eat_ty(&expected, line) {
            Ok(Some(t)) => return Ok(t),
            Err(e) => return Err(e),
            _ => {},
        }
        Err(parser_error::UnexpectedToken {
            found: try!(self.get_token()),
            expected: expected,
            line: self.line(),
            compiler_line: line,
        })
    }

    fn maybe_eat(&mut self, expected: token, line: u32) -> Result<Option<token>, parser_error> {
        self.maybe_eat_ty(&token_type::Specific(expected), line)
    }

    fn eat(&mut self, expected: token, line: u32) -> Result<token, parser_error> {
        self.eat_ty(token_type::Specific(expected), line)
    }

    fn parse_ident(&mut self) -> Result<String, parser_error> {
        match try!(self.get_token()) {
            token::Ident(s) => Ok(s),
            tok => {
                Err(parser_error::UnexpectedToken {
                    found: tok,
                    expected: token_type::Specific(token::Ident(String::new())),
                    line: self.line(),
                    compiler_line: line!(),
                })
            }
        }
    }

    fn maybe_parse_single_expr(&mut self) -> Result<Option<expr>, parser_error> {
        match try!(self.get_token()) {
            token::Ident(name) => {
                if let Some(_) = try!(self.maybe_eat(token::OpenParen, line!())) {
                    let mut args = Vec::new();
                    if let Some(e) = try!(self.maybe_parse_expr()) {
                        args.push(e);
                        while let Some(_) = try!(self.maybe_eat(token::Comma, line!())) {
                            args.push(try!(self.parse_expr()));
                        }
                    }
                    try!(self.eat(token::CloseParen, line!()));
                    Ok(Some(expr::Call {
                        name: name,
                        args: args,
                    }))
                } else {
                    Ok(Some(expr::Variable(name)))
                }
            }
            token::KeywordIf => {
                let condition = try!(self.parse_expr());
                try!(self.eat(token::OpenBrace, line!()));
                let if_value = try!(self.parse_expr());
                try!(self.eat(token::CloseBrace, line!()));
                try!(self.eat(token::KeywordElse, line!()));

                let else_value =
                match try!(self.eat_ty(token_type::AnyOf(
                        vec![token::OpenBrace, token::KeywordIf]), line!())) {
                    token::OpenBrace => {
                        let expr = try!(self.parse_expr());
                        try!(self.eat(token::CloseBrace, line!()));
                        expr
                    }
                    token::KeywordIf => {
                        self.unget_token(token::KeywordIf);
                        try!(self.parse_expr())
                    }
                    tok => unreachable!("{:?}", tok),
                };
                Ok(Some(expr::If {
                    condition: Box::new(condition),
                    then_value: Box::new(if_value),
                    else_value: Box::new(else_value),
                }))
            }
            token::Integer(value) => {
                Ok(Some(expr::Literal(value as u32)))
            }
            token::OpenParen => {
                let expr = try!(self.parse_expr());
                try!(self.eat(token::CloseParen, line!()));
                Ok(Some(expr))
            }
            token::Operand(operand::Minus) => {
                Ok(Some(expr::Minus(Box::new(try!(self.parse_single_expr())))))
            }
            token::Operand(operand::Plus) => {
                Ok(Some(expr::Plus(Box::new(try!(self.parse_single_expr())))))
            }
            token::Not => {
                Ok(Some(expr::Not(Box::new(try!(self.parse_single_expr())))))
            }
            token::KeywordTrue => Ok(Some(expr::Literal(1))),
            token::KeywordFalse => Ok(Some(expr::Literal(0))),
            tok => {
                self.unget_token(tok);
                Ok(None)
            }
        }
    }

    fn parse_single_expr(&mut self) -> Result<expr, parser_error> {
        match self.maybe_parse_single_expr() {
            Ok(Some(e)) => Ok(e),
            Ok(None) => Err(parser_error::UnexpectedToken {
                found: try!(self.get_token()),
                expected: token_type::Expression,
                line: self.line(),
                compiler_line: line!(),
            }),
            Err(e) => Err(e),
        }
    }

    fn maybe_parse_expr(&mut self) -> Result<Option<expr>, parser_error> {
        let lhs = match try!(self.maybe_parse_single_expr()) {
            Some(l) => l,
            None => return Ok(None),
        };
        match try!(self.maybe_eat_ty(&token_type::Operand, line!())) {
            Some(token::Operand(ref op)) => {
                self.parse_binop(lhs, op).map(|e| Some(e))
            }
            Some(tok) => unreachable!("{:?}", tok),
            None => {
                Ok(Some(lhs))
            }
        }
    }

    fn parse_expr(&mut self) -> Result<expr, parser_error> {
        let lhs = try!(self.parse_single_expr());
        match try!(self.maybe_eat_ty(&token_type::Operand, line!())) {
            Some(token::Operand(ref op)) => {
                self.parse_binop(lhs, op)
            }
            Some(tok) => unreachable!("{:?}", tok),
            None => {
                Ok(lhs)
            }
        }
    }

    fn parse_binop(&mut self, lhs: expr, left_op: &operand) -> Result<expr, parser_error> {
        let rhs = try!(self.parse_single_expr());
        match try!(self.maybe_eat_ty(&token_type::Operand, line!())) {
            Some(token::Operand(ref right_op)) => {
                if left_op.precedence() >= right_op.precedence() {
                    let new_lhs = left_op.expr(lhs, rhs);
                    self.parse_binop(new_lhs, right_op)
                } else {
                    let new_rhs = try!(self.parse_binop(rhs, right_op));
                    Ok(left_op.expr(lhs, new_rhs))
                }
            }
            Some(tok) => unreachable!("{:?}", tok),
            None => Ok(left_op.expr(lhs, rhs)),
        }
    }

    fn function(&mut self) -> Result<item, parser_error> {
        let name = try!(self.parse_ident());

        try!(self.eat(token::OpenParen, line!()));

        let mut args = Vec::new();
        match try!(self.get_token()) {
            token::Ident(arg) => {
                args.push(arg);
                loop {
                    let comma_or_close_paren = try!(self.get_token());
                    if let token::Comma = comma_or_close_paren {
                        args.push(try!(self.parse_ident()));
                    } else if let token::CloseParen = comma_or_close_paren {
                        break;
                    } else {
                        return Err(parser_error::UnexpectedToken {
                            found: comma_or_close_paren,
                            expected: token_type::AnyOf(vec![token::Comma, token::CloseParen]),
                            line: self.line(),
                            compiler_line: line!(),
                        });
                    }
                }
            }
            token::CloseParen => {}
            tok => {
                return Err(parser_error::UnexpectedToken {
                    found: tok,
                    expected: token_type::AnyOf(vec![token::Ident(String::new()),
                        token::CloseParen]),
                    line: self.line(),
                    compiler_line: line!(),
                });
            }
        }

        // TODO(ubsan): parse return
        try!(self.eat(token::OpenBrace, line!()));

        let mut body = Vec::new();
        loop {
            match try!(self.eat_ty(token_type::Statement, line!())) {
                token::KeywordReturn => {
                    body.push(stmt::Return(try!(self.parse_expr())));
                    try!(self.eat(token::Semicolon, line!()));
                }
                token::KeywordLet => {
                    let name = try!(self.parse_ident());
                    try!(self.eat(token::Equals, line!()));
                    let expr = try!(self.parse_expr());
                    body.push(stmt::Let {
                        name: name,
                        value: expr,
                    });
                    try!(self.eat(token::Semicolon, line!()));
                }
                token::CloseBrace => break,
                tok => unreachable!("{:?}", tok),
            }
        }

        Ok(item::Function { name: name, args: args, body: body })
    }
}
