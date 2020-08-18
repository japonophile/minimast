use std::env;
use std::fs;
use std::time::Instant;

macro_rules! check_bytes_left {
    ($i:ident, $b:ident) => {
        if $i >= $b.len() {
            return Err("Unexpected EOS".to_string())
        }
    }
}

fn skip_blanks(bytes: &[u8], mut i: usize) -> usize {
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

fn parse_constant(bytes: &[u8], mut i: usize) -> Result<(usize, String), String> {
    let start = i;
    loop {
        check_bytes_left!(i, bytes);
        if !is_math_symbol(bytes[i]) {
            break
        }
        i += 1;
    }
    Ok((i, format!("{}", String::from_utf8(bytes[start .. i].to_vec()).expect("Cannot convert to string"))))
}

fn parse_comment(bytes: &[u8], mut i: usize) -> Result<usize, String> {
    loop {
        check_bytes_left!(i, bytes);
        if bytes[i] == '$' as u8 {
            i += 1;
            check_bytes_left!(i, bytes);
            if bytes[i] == '(' as u8 {
                return Err("Comments may not be nested".to_string())
            }
            if bytes[i] == ')' as u8 {
                i += 1;
                break
            }
        }
        i += 1
    }
    Ok(i)
}

fn parse_constant_stmt(bytes: &[u8], mut i: usize) -> Result<usize, String> {
    loop {
        check_bytes_left!(i, bytes);
        i = skip_blanks(bytes, i);
        if bytes[i] == '$' as u8 {
            i += 1;
            check_bytes_left!(i, bytes);
            if bytes[i] == '(' as u8 {
                i += 1;
                match parse_comment(bytes, i) {
                    Ok(ni) => i = ni,
                    Err(e) => return Err(e)
                }
            }
            else if bytes[i] == '.' as u8 {
                i += 1;
                break
            }
            else {
                return Err(format!("Unexpected token ${}", bytes[i] as char))
            }
        }
        else {
            match parse_constant(bytes, i) {
                Ok((ni, c)) => { print!("{} ", c); i = ni },
                Err(e) => return Err(e)
            }
        }
    }
    Ok(i)
}

fn parse_metamath(filename: &str) -> Result<(), String> {
    let now = Instant::now();
    let program = fs::read_to_string(filename).expect("Could not read file");
    let bytes = program.as_bytes();
    let mut i: usize = 0;
    let mut n = 0;
    loop {
        if i >= bytes.len() {
            break
        }
        if bytes[i] == '$' as u8 {
            n += 1;
            i += 1;
            check_bytes_left!(i, bytes);
            if bytes[i] == '(' as u8 {
                i += 1;
                match parse_comment(bytes, i) {
                    Ok(ni) => i = ni,
                    Err(e) => return Err(e)
                }
            }
            else if bytes[i] == 'c' as u8 {
                i += 1;
                match parse_constant_stmt(bytes, i) {
                    Ok(ni) => i = ni,
                    Err(e) => return Err(e)
                }
            }
        }
        i += 1
    }
    println!("");
    println!("{} characters read, {} tags found", program.len(), n);
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
