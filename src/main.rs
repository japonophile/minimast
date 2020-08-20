use std::collections::HashMap;
use std::collections::HashSet;
use std::env;
use std::fs;
use std::time::Instant;

pub struct Scope {
    pub variables: HashSet<u32>
}

pub struct Program {
    pub n_stmt: u32,
    pub constants: HashMap<String, u32>,
    pub variables: HashMap<String, u32>,
    pub labels: HashMap<String, u32>
}

pub struct ParserState {
    pub program: Program,
    pub scope: Scope
}

pub struct ParseBuffer<'a> {
    pub bytes: &'a [u8],
    pub i: usize
}

impl Clone for Scope {
    fn clone(&self) -> Scope {
        Scope {
            variables: self.variables.clone()
        }
    }
}

macro_rules! check_bytes_left {
    ($b:ident) => {
        if $b.i >= $b.bytes.len() {
            return Err("Unexpected EOS".to_string())
        }
    }
}

macro_rules! skip_comment {
    ($b:ident) => {
        if $b.bytes[$b.i] as char == '(' {
            $b.i += 1;
            match parse_comment($b) {
                Ok(()) => continue,
                Err(e) => return Err(e)
            }
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

fn is_math_symbol(byte: u8) -> bool {
    return byte >= 0x21 && byte <= 0x7e && byte != '$' as u8
}

fn parse_constant(b: &mut ParseBuffer, mut state: ParserState) -> Result<ParserState, String> {
    let start = b.i;
    loop {
        check_bytes_left!(b);
        if !is_math_symbol(b.bytes[b.i]) {
            break
        }
        b.i += 1;
    }
    let constant = String::from_utf8(b.bytes[start .. b.i].to_vec()).expect("Cannot convert to string");
    if state.program.constants.contains_key(&constant) {
        return Err(format!("Constant {} was already defined before", constant));
    }
    if state.program.variables.contains_key(&constant) {
        return Err(format!("Constant {} was previously defined as a variable", constant));
    }
    if state.program.labels.contains_key(&constant) {
        return Err(format!("Constant {} matches an existing label", constant));
    }
    state.program.constants.insert(constant, state.program.constants.len() as u32);
    Ok(state)
}

fn parse_variable(b: &mut ParseBuffer, mut state: ParserState) -> Result<ParserState, String> {
    let start = b.i;
    loop {
        check_bytes_left!(b);
        if !is_math_symbol(b.bytes[b.i]) {
            break
        }
        b.i += 1;
    }
    let variable = String::from_utf8(b.bytes[start .. b.i].to_vec()).expect("Cannot convert to string");
    if state.program.constants.contains_key(&variable) {
        return Err(format!("Variable {} matches an existing constant", variable));
    }
    if state.program.labels.contains_key(&variable) {
        return Err(format!("Variable {} matches an existing label", variable));
    }
    let v: u32;
    if state.program.variables.contains_key(&variable) {
        v = state.program.variables[&variable];
        if state.scope.variables.contains(&v) {
            return Err(format!("Variable {} was already defined before", variable));
        }
    }
    else {
        v = state.program.variables.len() as u32;
        state.program.variables.insert(variable, v);
    }
    state.scope.variables.insert(v);
    Ok(state)
}

fn parse_label(b: &mut ParseBuffer, mut state: ParserState) -> Result<(ParserState, u32), String> {
    let start = b.i;
    loop {
        check_bytes_left!(b);
        let c = char::from(b.bytes[b.i]);
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
    if state.program.constants.contains_key(&label) {
        return Err(format!("Label {} matches a constant", label));
    }
    if state.program.variables.contains_key(&label) {
        return Err(format!("Label {} matches a variable", label));
    }
    let l = state.program.labels.len() as u32;
    state.program.labels.insert(label, l);
    Ok((state, l))
}

fn parse_comment(b: &mut ParseBuffer) -> Result<(), String> {
    loop {
        check_bytes_left!(b);
        if b.bytes[b.i] as char == '$' {
            b.i += 1;
            check_bytes_left!(b);
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

fn parse_const_var_stmt(b: &mut ParseBuffer, parse_element: fn(&mut ParseBuffer, ParserState) -> Result<ParserState, String>, mut state: ParserState) -> Result<ParserState, String> {
    state.program.n_stmt += 1;
    loop {
        skip_blanks(b);
        check_bytes_left!(b);
        if b.bytes[b.i] as char == '$' {
            b.i += 1;
            check_bytes_left!(b);
            skip_comment!(b);
            if b.bytes[b.i] as char == '.' {
                b.i += 1;
                break
            }
            else {
                return Err(format!("Unexpected token ${}", b.bytes[b.i] as char))
            }
        }
        else {
            match parse_element(b, state) {
                Ok(ns) => state = ns,
                Err(e) => return Err(e)
            }
        }
    }
    Ok(state)
}

fn parse_xxx_stmt(b: &mut ParseBuffer, mut state: ParserState) -> Result<ParserState, String> {
    loop {
        skip_blanks(b);
        check_bytes_left!(b);
        if b.bytes[b.i] as char == '$' {
            b.i += 1;
            check_bytes_left!(b);
            if b.bytes[b.i] as char == '.' {
                b.i += 1;
                break
            }
        }
        b.i += 1;
    }
    state.program.n_stmt += 1;
    Ok(state)
}

fn parse_labeled_stmt(b: &mut ParseBuffer, mut state: ParserState) -> Result<ParserState, String> {
    let label: u32;

    skip_blanks(b);
    check_bytes_left!(b);
    match parse_label(b, state) {
        Ok((ns, l)) => { state = ns; label = l },
        Err(e) => return Err(e)
    }
    // println!("{}", label);

    loop {
        skip_blanks(b);
        check_bytes_left!(b);
        if b.bytes[b.i] as char == '$' {
            b.i += 1;
            check_bytes_left!(b);
            skip_comment!(b);
            if b.bytes[b.i] as char == 'f' {
                b.i += 1;
                // parse floating statement
                return parse_xxx_stmt(b, state);
            }
            else if b.bytes[b.i] as char == 'e' {
                b.i += 1;
                // parse essential statement
                return parse_xxx_stmt(b, state);
            }
            else if b.bytes[b.i] as char == 'a' {
                b.i += 1;
                // parse axiom statement
                return parse_xxx_stmt(b, state);
            }
            else if b.bytes[b.i] as char == 'p' {
                b.i += 1;
                // parse provable statement
                return parse_xxx_stmt(b, state);
            }
            else {
                return Err(format!("Unexpected token ${}", b.bytes[b.i] as char))
            }
        }
        else {
            return Err(format!("Unexpected token {}", b.bytes[b.i] as char))
        }
    }
}

fn parse_stmt(b: &mut ParseBuffer, state: ParserState) -> Result<ParserState, String> {
    loop {
        skip_blanks(b);
        check_bytes_left!(b);
        if b.bytes[b.i] as char == '$' {
            b.i += 1;
            check_bytes_left!(b);
            skip_comment!(b);
            if b.bytes[b.i] as char == '{' {
                b.i += 1;
                let original_scope = state.scope.clone();
                match parse_block(b, state) {
                    Ok(mut ns) => { ns.scope = original_scope; return Ok(ns) },
                    Err(e) => return Err(e)
                }
            }
            if b.bytes[b.i] as char == 'v' {
                b.i += 1;
                return parse_const_var_stmt(b, parse_variable, state);
            }
            else if b.bytes[b.i] as char == 'd' {
                b.i += 1;
                // parse disjoint statement
                return parse_xxx_stmt(b, state);
            }
            else {
                b.i -= 1;
            }
        }
        return parse_labeled_stmt(b, state);
    }
}

fn parse_block(b: &mut ParseBuffer, mut state: ParserState) -> Result<ParserState, String> {
    loop {
        skip_blanks(b);
        check_bytes_left!(b);
        if b.bytes[b.i] as char == '$' {
            b.i += 1;
            check_bytes_left!(b);
            skip_comment!(b);
            if b.bytes[b.i] as char == '}' {
                b.i += 1;
                break
            }
            else {
                b.i -= 1;
            }
        }
        match parse_stmt(b, state) {
            Ok(ns) => state = ns,
            Err(e) => return Err(e)
        }
    }
    state.program.n_stmt += 1;
    Ok(state)
}

fn parse_top_level(b: &mut ParseBuffer, mut state: ParserState) -> Result<ParserState, String> {
    loop {
        skip_blanks(b);
        if b.i >= b.bytes.len() {
            break
        }
        if b.bytes[b.i] as char == '$' {
            b.i += 1;
            check_bytes_left!(b);
            skip_comment!(b);
            if b.bytes[b.i] as char == 'c' {
                b.i += 1;
                match parse_const_var_stmt(b, parse_constant, state) {
                    Ok(ns) => state = ns,
                    Err(e) => return Err(e)
                }
                continue
            }
            else if b.bytes[b.i] as char == '{' {
                b.i += 1;
                let original_scope = state.scope.clone();
                match parse_block(b, state) {
                    Ok(ns) => { state = ns; state.scope = original_scope },
                    Err(e) => return Err(e)
                }
                continue
            }
            else {
                b.i -= 1;
            }
        }
        match parse_stmt(b, state) {
            Ok(ns) => state = ns,
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
            constants: HashMap::new(),
            variables: HashMap::new(),
            labels: HashMap::new()
        },
        scope: Scope {
            variables: HashSet::new()
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
    // println!("Constants: {:?}", state.program.constants.keys())
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
