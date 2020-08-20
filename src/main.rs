use std::collections::HashMap;
use std::collections::HashSet;
use std::env;
use std::fs;
use std::time::Instant;

type Symbol = u32;
type Constant = Symbol;
type Variable = Symbol;
type Label = u32;

#[derive(Clone)]
pub struct Floating {
    pub typ: Constant,
    pub var: Variable
}

pub struct TypedSymbols {
    pub typ: Constant,
    pub syms: Vec<Symbol>
}

pub struct Scope {
    pub variables: HashSet<Variable>,
    pub vartypes: HashMap<Variable, Constant>,
    pub floatings: HashMap<Label, Floating>,
    pub essentials: HashMap<Label, TypedSymbols>,
    pub disjoints: HashSet<(Variable, Variable)>
}

#[derive(Clone)]
pub enum ProofStep {
    Label(Label),
    Save(),
    Load(usize),
    Unknown()
}

pub enum Proof {
    Uncompressed {
        labels: Vec<ProofStep>
    },
    Compressed {
        labels: Vec<Label>,
        chars: String
    }
}

pub struct Assertion {
    pub ax: TypedSymbols,
    pub proof: Option<Proof>,
    pub scope: Scope
}

pub struct Program {
    pub n_stmt: u32,
    pub constants: HashSet<Constant>,
    pub variables: HashSet<Variable>,
    pub symbols: HashMap<String, Symbol>,
    pub labels: HashMap<String, Label>,
    pub vartypes: HashMap<Variable, Constant>,
    pub axioms: HashMap<Label, Assertion>,
    pub provables: HashMap<Label, Assertion>,
}

pub struct ParserState {
    pub program: Program,
    pub scope: Scope
}

pub struct ParseBuffer<'a> {
    pub bytes: &'a [u8],
    pub i: usize
}

impl Clone for TypedSymbols {
    fn clone(&self) -> TypedSymbols {
        TypedSymbols {
            typ: self.typ.clone(),
            syms: self.syms.clone()
        }
    }
}

impl Clone for Scope {
    fn clone(&self) -> Scope {
        Scope {
            variables: self.variables.clone(),
            vartypes: self.vartypes.clone(),
            floatings: self.floatings.clone(),
            essentials: self.essentials.clone(),
            disjoints: self.disjoints.clone()
        }
    }
}

macro_rules! require_another_byte {
    ($b:ident) => {
        if $b.i >= $b.bytes.len() {
            return Err("Unexpected EOS".to_string())
        }
    }
}

fn skip_blanks(b: &mut ParseBuffer) {
    loop {
        if b.i >= b.bytes.len() {
            break
        }
        match b.bytes[b.i] as char {
            ' ' | '\t' | '\r' | '\n' => b.i += 1,
            _ => break
        }
    }
}

enum Token {
    StartBlock,
    EndBlock,
    StartConstant,
    StartVariable,
    StartFloating,
    StartEssential,
    StartDisjoint,
    StartAxiom,
    StartProvable,
    StartProof,
    EndStatement,
    Other,
    Empty
}

fn parse_token(b: &mut ParseBuffer, allow_empty: bool) -> Result<Token, String> {
    loop {
        if allow_empty && b.i >= b.bytes.len() {
            return Ok(Token::Empty)
        }
        require_another_byte!(b);
        if b.bytes[b.i] as char == '$' {
            b.i += 1;
            require_another_byte!(b);
            let c = b.bytes[b.i] as char;
            b.i += 1;
            match c {
                '(' => match parse_comment(b) {
                    Ok(()) => { skip_blanks(b); continue },
                    Err(e) => return Err(e) },
                '{' => return Ok(Token::StartBlock),
                '}' => return Ok(Token::EndBlock),
                'c' => return Ok(Token::StartConstant),
                'v' => return Ok(Token::StartVariable),
                'f' => return Ok(Token::StartFloating),
                'e' => return Ok(Token::StartEssential),
                'd' => return Ok(Token::StartDisjoint),
                'a' => return Ok(Token::StartAxiom),
                'p' => return Ok(Token::StartProvable),
                '=' => return Ok(Token::StartProof),
                '.' => return Ok(Token::EndStatement),
                _ => return Err(format!("Unexpected token ${}", c))
            }
        }
        return Ok(Token::Other)
    }
}

fn read_next_token(b: &mut ParseBuffer) -> Result<Token, String> {
    return parse_token(b, false)
}

fn read_next_token_if_exists(b: &mut ParseBuffer) -> Result<Token, String> {
    return parse_token(b, true)
}

fn is_math_symbol(byte: u8) -> bool {
    return byte >= 0x21 && byte <= 0x7e && byte != '$' as u8
}

fn parse_symbol(b: &mut ParseBuffer) -> Result<String, String> {
    let start = b.i;
    loop {
        require_another_byte!(b);
        if !is_math_symbol(b.bytes[b.i]) {
            break
        }
        b.i += 1;
    }
    if start == b.i {
        println!("Empty symbol found: {:?}",
                 String::from_utf8(b.bytes[start .. start + 10].to_vec()).expect("Cannot convert to string"));
    }
    let symbol = String::from_utf8(b.bytes[start .. b.i].to_vec()).expect("Cannot convert to string");
    Ok(symbol)
}

fn register_constant(constant: String, mut state: ParserState) -> Result<ParserState, String> {
    if state.program.symbols.contains_key(&constant) {
        return Err(format!("Constant {} was already defined before", constant));
    }
    if state.program.labels.contains_key(&constant) {
        return Err(format!("Constant {} matches an existing label", constant));
    }
    let s = state.program.symbols.len() as Symbol;
    state.program.symbols.insert(constant, s);
    state.program.constants.insert(s as Constant);
    Ok(state)
}

fn register_variable(variable: String, mut state: ParserState) -> Result<ParserState, String> {
    if state.program.labels.contains_key(&variable) {
        return Err(format!("Variable {} matches an existing label", variable));
    }
    let s: Symbol;
    if state.program.symbols.contains_key(&variable) {
        s = state.program.symbols[&variable];
        if state.program.constants.contains(&s) {
            return Err(format!("Variable {} matches an existing constant", variable));
        }
        if state.scope.variables.contains(&s) {
            return Err(format!("Variable {} was already defined before", variable));
        }
        if !state.program.variables.contains(&s) {
            return Err(format!("Variable {} already defined but is not in the set of variables", variable));
        }
    }
    else {
        s = state.program.symbols.len() as Symbol;
        state.program.symbols.insert(variable, s);
        state.program.variables.insert(s as Variable);
    }
    state.scope.variables.insert(s as Variable);
    Ok(state)
}

fn parse_label(b: &mut ParseBuffer, mut state: ParserState) -> Result<(ParserState, Label), String> {
    let start = b.i;
    loop {
        require_another_byte!(b);
        let c = b.bytes[b.i] as char;
        if !c.is_ascii_alphanumeric() &&
           c != '.' && c != '-' && c != '_' {
            break
        }
        b.i += 1;
    }
    let label = String::from_utf8(b.bytes[start .. b.i].to_vec()).expect("Cannot convert to string");
    if state.program.labels.contains_key(&label) {
        return Err(format!("Label {} was already defined before", label));
    }
    if state.program.symbols.contains_key(&label) {
        return Err(format!("Label {} matches a constant or variable", label));
    }
    let l = state.program.labels.len() as Label;
    state.program.labels.insert(label, l);
    Ok((state, l))
}

fn parse_comment(b: &mut ParseBuffer) -> Result<(), String> {
    loop {
        require_another_byte!(b);
        if b.bytes[b.i] as char == '$' {
            b.i += 1;
            require_another_byte!(b);
            if b.bytes[b.i] as char == '(' {
                return Err("Comments may not be nested".to_string())
            }
            if b.bytes[b.i] as char == ')' {
                b.i += 1;
                break
            }
        }
        b.i += 1
    }
    Ok(())
}

fn parse_const_var_stmt(b: &mut ParseBuffer, register_symbol: fn(String, ParserState) -> Result<ParserState, String>, mut state: ParserState) -> Result<ParserState, String> {
    state.program.n_stmt += 1;
    loop {
        skip_blanks(b);
        match read_next_token(b) {
            Ok(Token::EndStatement) => break,
            Ok(Token::Other) => {
                match parse_symbol(b) {
                    Ok(symbol) => {
                        match register_symbol(symbol, state) {
                            Ok(ns) => { state = ns; continue },
                            Err(e) => return Err(e) } },
                    Err(e) => return Err(e) } },
            Ok(_) => return Err(format!("Unexpected token ${}", b.bytes[b.i - 1] as char)),
            Err(e) => return Err(e)
        }
    }
    Ok(state)
}

fn get_constant(constant: &String, program: &Program) -> Option<Constant> {
    if !program.symbols.contains_key(constant) {
        return None;
    }
    let c = program.symbols[constant] as Constant;
    if !program.constants.contains(&c) {
        return None;
    }
    Some(c)
}

fn get_variable(variable: &String, state: &ParserState) -> Option<Variable> {
    if !state.program.symbols.contains_key(variable) {
        return None;
    }
    let v = state.program.symbols[variable] as Variable;
    if !state.program.variables.contains(&v) {
        return None;
    }
    if !state.scope.variables.contains(&v) {
        return None;
    }
    Some(v)
}

fn parse_floating_stmt(b: &mut ParseBuffer, label: Label, mut state: ParserState) -> Result<ParserState, String> {
    let typ: Constant;
    let var: Variable;
    skip_blanks(b);
    match parse_symbol(b) {
        Ok(typecode) => {
            match get_constant(&typecode, &state.program) {
                Some(t) => typ = t,
                None => return Err(format!("Type {} not found in constants", typecode))
            } },
        Err(e) => return Err(e)
    }
    skip_blanks(b);
    match parse_symbol(b) {
        Ok(variable) => {
            match get_variable(&variable, &state) {
                Some(v) => var = v,
                None => return Err(format!("Variable {} not defined", variable))
            } },
        Err(e) => return Err(e)
    }
    skip_blanks(b);
    match read_next_token(b) {
        Ok(Token::EndStatement) => {},
        Ok(_) => return Err(format!("Unexpected token ${}", b.bytes[b.i - 1] as char)),
        Err(e) => return Err(e)
    }
    if state.scope.vartypes.contains_key(&var) {
        return Err(format!("Variable {} already has a type", var))
    }
    if state.program.vartypes.contains_key(&var) &&
        state.program.vartypes[&var] != typ {
            return Err(format!("Variable {} was previously assigned a different type", var))
        }
    state.program.vartypes.insert(var, typ);
    state.scope.vartypes.insert(var, typ);
    state.scope.floatings.insert(label, Floating { typ: typ, var: var });
    state.program.n_stmt += 1;
    Ok(state)
}

fn parse_xxx_stmt(b: &mut ParseBuffer, mut state: ParserState) -> Result<ParserState, String> {
    loop {
        skip_blanks(b);
        match read_next_token(b) {
            Ok(Token::EndStatement) => break,
            Err(e) => return Err(e),
            _ => b.i += 1  // TODO
        }
    }
    state.program.n_stmt += 1;
    Ok(state)
}

fn parse_labeled_stmt(b: &mut ParseBuffer, mut state: ParserState) -> Result<ParserState, String> {
    let label: Label;

    skip_blanks(b);
    require_another_byte!(b);
    match parse_label(b, state) {
        Ok((ns, l)) => { state = ns; label = l },
        Err(e) => return Err(e)
    }
    // println!("{} ({})", label, b.i);

    loop {
        skip_blanks(b);
        match read_next_token(b) {
            Ok(Token::StartFloating) => return parse_floating_stmt(b, label, state),
            Ok(Token::StartEssential) => return parse_xxx_stmt(b, state),
            Ok(Token::StartAxiom) => return parse_xxx_stmt(b, state),
            Ok(Token::StartProvable) => return parse_xxx_stmt(b, state),
            Ok(Token::Other) => return Err(format!("Unexpected token {}", b.bytes[b.i] as char)),
            Ok(_) => return Err(format!("Unexpected token ${}", b.bytes[b.i - 1] as char)),
            Err(e) => return Err(e)
        }
    }
}

fn parse_stmt(b: &mut ParseBuffer, state: ParserState) -> Result<ParserState, String> {
    skip_blanks(b);
    match read_next_token(b) {
        Ok(Token::StartBlock) => {
            let original_scope = state.scope.clone();
            match parse_block(b, state) {
                Ok(mut ns) => { ns.scope = original_scope; return Ok(ns) },
                Err(e) => return Err(e)
            } },
        Ok(Token::StartVariable) => return parse_const_var_stmt(b, register_variable, state),
        Ok(Token::StartDisjoint) => return parse_xxx_stmt(b, state),
        Ok(Token::Other) => {},
        Ok(_) => b.i -= 2,  // rewind parsed token
        Err(e) => return Err(e),
    }
    return parse_labeled_stmt(b, state)
}

fn parse_block(b: &mut ParseBuffer, mut state: ParserState) -> Result<ParserState, String> {
    loop {
        skip_blanks(b);
        match read_next_token(b) {
            Ok(Token::EndBlock) => break,
            Ok(Token::Other) => {},
            Ok(_) => b.i -= 2,  // rewind parsed token
            Err(e) => return Err(e),
        }
        match parse_stmt(b, state) {
            Ok(ns) => { state = ns; continue },
            Err(e) => return Err(e)
        }
    }
    state.program.n_stmt += 1;
    Ok(state)
}

fn parse_top_level(b: &mut ParseBuffer, mut state: ParserState) -> Result<ParserState, String> {
    loop {
        skip_blanks(b);
        match read_next_token_if_exists(b) {
            Ok(Token::StartConstant) => match parse_const_var_stmt(b, register_constant, state) {
                Ok(ns) => { state = ns; continue },
                Err(e) => return Err(e) },
            Ok(Token::Other) => {},
            Ok(Token::Empty) => break,
            Ok(_) => b.i -= 2,  // rewind parsed token
            Err(e) => return Err(e),
        }
        match parse_stmt(b, state) {
            Ok(ns) => { state = ns; continue },
            Err(e) => return Err(e)
        }
    }
    println!("{} bytes were read into the source buffer.", b.bytes.len());
    println!("The source has {} statements;", state.program.n_stmt);
    Ok(state)
}

fn parse_metamath(filename: &str) -> Result<(), String> {
    let now = Instant::now();
    let mut state = ParserState {
        program: Program {
            n_stmt: 0,
            constants: HashSet::new(),
            variables: HashSet::new(),
            symbols: HashMap::new(),
            labels: HashMap::new(),
            vartypes: HashMap::new(),
            axioms: HashMap::new(),
            provables: HashMap::new()
        },
        scope: Scope {
            variables: HashSet::new(),
            vartypes: HashMap::new(),
            floatings: HashMap::new(),
            essentials: HashMap::new(),
            disjoints: HashSet::new()
        }
    };
    print!("Reading source file \"{}\"... ", filename);
    let program_text = fs::read_to_string(filename).expect("Could not read file");
    let mut b = ParseBuffer {
        bytes: program_text.as_bytes(),
        i: 0
    };
    println!("{} bytes", b.bytes.len());
    match parse_top_level(&mut b, state) {
        Ok(ns) => state = ns,
        Err(e) => return Err(e)
    }
    // println!("Constants: {:?}", state.program.constants.keys());
    println!("{} constants", state.program.constants.len());
    println!("{} variables", state.program.variables.len());
    println!("{} labels", state.program.labels.len());
    println!("Program parsed in {} msec", now.elapsed().subsec_millis());
    Ok(())
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let filename = &args[1];
    match parse_metamath(filename.as_str()) {
        Ok(_) => println!("OK"),
        Err(e) => println!("Error: {}", e)
    }
    println!("Done");
}
