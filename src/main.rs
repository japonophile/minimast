use std::collections::HashMap;
use std::env;
use std::fs;
use std::time::Instant;

pub struct Program {
    pub n_stmt: u32,
    pub constants: HashMap<String, u32>
}

pub struct ParserState {
    pub i: usize,
    pub program: Program
}

macro_rules! check_bytes_left {
    ($i:ident, $b:ident) => {
        if *$i >= $b.len() {
            return Err("Unexpected EOS".to_string())
        }
    }
}

macro_rules! skip_comment {
    ($i:ident, $b:ident) => {
        if $b[*$i] == '(' as u8 {
            *$i += 1;
            match parse_comment($b, *$i) {
                Ok(ni) => *$i = ni,
                Err(e) => return Err(e)
            }
            continue
        }
    }
}

fn skip_blanks(bytes: &[u8], start: usize) -> usize {
    let mut i = start;
    loop {
        if i >= bytes.len() {
            break
        }
        if bytes[i] == ' ' as u8 ||
           bytes[i] == '\t' as u8 ||
           bytes[i] == '\r' as u8 ||
           bytes[i] == '\n' as u8 {
            i += 1;
            continue
        }
        break
    }
    i
}

fn is_math_symbol(byte: u8) -> bool {
    return byte >= 0x21 && byte <= 0x7e && byte != '$' as u8
}

fn parse_constant(bytes: &[u8], mut state: ParserState) -> Result<ParserState, String> {
    let i = &mut state.i;
    let start = *i;
    loop {
        check_bytes_left!(i, bytes);
        if !is_math_symbol(bytes[*i]) {
            break
        }
        *i += 1;
    }
    let constant = String::from_utf8(bytes[start .. *i].to_vec()).expect("Cannot convert to string");
    if state.program.constants.contains_key(&constant) {
        return Err(format!("Constant {} was already defined before", constant));
    }
    state.program.constants.insert(constant, state.program.constants.len() as u32);
    Ok(state)
}

fn parse_label(bytes: &[u8], start: usize) -> Result<(usize, String), String> {
    let mut j = start;
    let i = &mut j;
    loop {
        check_bytes_left!(i, bytes);
        let c = char::from(bytes[*i]);
        if !c.is_ascii_alphanumeric() &&
           c != '.' && c != '-' && c != '_' {
            break
        }
        *i += 1;
    }
    let label = String::from_utf8(bytes[start .. *i].to_vec()).expect("Cannot convert to string");
    Ok((*i, label))
}



fn parse_comment(bytes: &[u8], start: usize) -> Result<usize, String> {
    let mut j = start;
    let i = &mut j;
    loop {
        check_bytes_left!(i, bytes);
        if bytes[*i] == '$' as u8 {
            *i += 1;
            check_bytes_left!(i, bytes);
            if bytes[*i] == '(' as u8 {
                return Err("Comments may not be nested".to_string())
            }
            if bytes[*i] == ')' as u8 {
                *i += 1;
                break
            }
        }
        *i += 1
    }
    Ok(*i)
}

fn parse_constant_stmt(bytes: &[u8], mut state: ParserState) -> Result<ParserState, String> {
    state.program.n_stmt += 1;
    let mut i = &mut state.i;
    loop {
        *i = skip_blanks(bytes, *i);
        check_bytes_left!(i, bytes);
        if bytes[*i] == '$' as u8 {
            *i += 1;
            check_bytes_left!(i, bytes);
            skip_comment!(i, bytes);
            if bytes[*i] == '.' as u8 {
                *i += 1;
                break
            }
            else {
                return Err(format!("Unexpected token ${}", bytes[*i] as char))
            }
        }
        else {
            match parse_constant(bytes, state) {
                Ok(ns) => { state = ns; i = &mut state.i },
                Err(e) => return Err(e)
            }
        }
    }
    Ok(state)
}

fn parse_xxx_stmt(bytes: &[u8], mut state: ParserState) -> Result<ParserState, String> {
    let i = &mut state.i;
    loop {
        *i = skip_blanks(bytes, *i);
        check_bytes_left!(i, bytes);
        if bytes[*i] == '$' as u8 {
            *i += 1;
            check_bytes_left!(i, bytes);
            if bytes[*i] == '.' as u8 {
                *i += 1;
                break
            }
        }
        *i += 1;
    }
    state.program.n_stmt += 1;
    Ok(state)
}

fn parse_labeled_stmt(bytes: &[u8], mut state: ParserState) -> Result<ParserState, String> {
    let i = &mut state.i;
    let label: String;

    *i = skip_blanks(bytes, *i);
    check_bytes_left!(i, bytes);
    match parse_label(bytes, *i) {
        Ok((ni, l)) => { label = l; *i = ni },
        Err(e) => return Err(e)
    }
    // println!("{}", label);

    loop {
        *i = skip_blanks(bytes, *i);
        check_bytes_left!(i, bytes);
        if bytes[*i] == '$' as u8 {
            *i += 1;
            check_bytes_left!(i, bytes);
            skip_comment!(i, bytes);
            if bytes[*i] == 'f' as u8 {
                *i += 1;
                // parse floating statement
                return parse_xxx_stmt(bytes, state);
            }
            else if bytes[*i] == 'e' as u8 {
                *i += 1;
                // parse essential statement
                return parse_xxx_stmt(bytes, state);
            }
            else if bytes[*i] == 'a' as u8 {
                *i += 1;
                // parse axiom statement
                return parse_xxx_stmt(bytes, state);
            }
            else if bytes[*i] == 'p' as u8 {
                *i += 1;
                // parse provable statement
                return parse_xxx_stmt(bytes, state);
            }
            else {
                return Err(format!("Unexpected token ${}", bytes[*i] as char))
            }
        }
        else {
            return Err(format!("Unexpected token {}", bytes[*i] as char))
        }
    }
}

fn parse_stmt(bytes: &[u8], mut state: ParserState) -> Result<ParserState, String> {
    let i = &mut state.i;
    loop {
        *i = skip_blanks(bytes, *i);
        check_bytes_left!(i, bytes);
        if bytes[*i] == '$' as u8 {
            *i += 1;
            check_bytes_left!(i, bytes);
            skip_comment!(i, bytes);
            if bytes[*i] == '{' as u8 {
                *i += 1;
                return parse_block(bytes, state);
            }
            if bytes[*i] == 'v' as u8 {
                *i += 1;
                // parse variable statement
                return parse_xxx_stmt(bytes, state);
            }
            else if bytes[*i] == 'd' as u8 {
                *i += 1;
                // parse disjoint statement
                return parse_xxx_stmt(bytes, state);
            }
            else {
                *i -= 1;
            }
        }
        return parse_labeled_stmt(bytes, state);
    }
}

fn parse_block(bytes: &[u8], mut state: ParserState) -> Result<ParserState, String> {
    let mut i = &mut state.i;
    loop {
        *i = skip_blanks(bytes, *i);
        check_bytes_left!(i, bytes);
        if bytes[*i] == '$' as u8 {
            *i += 1;
            check_bytes_left!(i, bytes);
            skip_comment!(i, bytes);
            if bytes[*i] == '}' as u8 {
                *i += 1;
                break
            }
            else {
                *i -= 1;
            }
        }
        match parse_stmt(bytes, state) {
            Ok(ns) => { state = ns; i = &mut state.i },
            Err(e) => return Err(e)
        }
    }
    state.program.n_stmt += 1;
    Ok(state)
}

fn parse_top_level(bytes: &[u8], mut state: ParserState) -> Result<ParserState, String> {
    let mut i = &mut state.i;
    loop {
        *i = skip_blanks(bytes, *i);
        if *i >= bytes.len() {
            break
        }
        if bytes[*i] == '$' as u8 {
            *i += 1;
            check_bytes_left!(i, bytes);
            skip_comment!(i, bytes);
            if bytes[*i] == 'c' as u8 {
                *i += 1;
                match parse_constant_stmt(bytes, state) {
                    Ok(ns) => { state = ns; i = &mut state.i },
                    Err(e) => return Err(e)
                }
                continue
            }
            else if bytes[*i] == '{' as u8 {
                *i += 1;
                match parse_block(bytes, state) {
                    Ok(ns) => { state = ns; i = &mut state.i },
                    Err(e) => return Err(e)
                }
                continue
            }
            else {
                *i -= 1;
            }
        }
        match parse_stmt(bytes, state) {
            Ok(ns) => { state = ns; i = &mut state.i },
            Err(e) => return Err(e)
        }
    }
    println!("{} bytes were read into the source buffer.", bytes.len());
    println!("The source has {} statements;", state.program.n_stmt);
    Ok(state)
}

fn parse_metamath(filename: &str) -> Result<(), String> {
    let now = Instant::now();
    let mut state = ParserState {
        i: 0,
        program: Program {
            n_stmt: 0,
            constants: HashMap::new()
        }
    };
    print!("Reading source file \"{}\"... ", filename);
    let program_text = fs::read_to_string(filename).expect("Could not read file");
    let bytes = program_text.as_bytes();
    println!("{} bytes", bytes.len());
    match parse_top_level(bytes, state) {
        Ok(ns) => {
            state = ns;
            // println!("Constants: {:?}", state.program.constants.keys())
            println!("{} constants", state.program.constants.len())
        },
        Err(e) => println!("Error: {}", e)
    }
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
