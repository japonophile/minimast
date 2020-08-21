use itertools::Itertools;
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
    Floating(Label),
    Essential(Label),
    Axiom(Label),
    Provable(Label),
    Save(),
    Load(usize),
    Unknown()
}

type Proof = Vec<ProofStep>;

pub struct Assertion {
    pub ax: TypedSymbols,
    pub proof: Option<Proof>,
    pub scope: Scope,
    pub mvars: HashSet<Variable>,
    pub mhyps: Vec<Label>,
    pub mdisj: HashSet<(Variable, Variable)>,
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
    pub scope: Scope,
}

pub struct ParseBuffer<'a> {
    pub bytes: &'a [u8],
    pub i: usize,
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

#[derive(PartialEq)]
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
    OtherNotRead,
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
        return Ok(Token::OtherNotRead)
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

fn parse_label(b: &mut ParseBuffer) -> Result<String, String> {
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
    Ok(label)
}

fn register_label(label: String, mut state: ParserState) -> Result<(ParserState, Label), String> {
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
    loop {
        skip_blanks(b);
        match read_next_token(b) {
            Ok(Token::EndStatement) => break,
            Ok(Token::OtherNotRead) => match parse_symbol(b) {
                Ok(symbol) => match register_symbol(symbol, state) {
                    Ok(ns) => { state = ns; continue },
                    Err(e) => return Err(e) },
                Err(e) => return Err(e) },
            Ok(_) => return Err(format!("Unexpected token ${}", b.bytes[b.i - 1] as char)),
            Err(e) => return Err(e)
        }
    }
    state.program.n_stmt += 1;
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

fn parse_floating(b: &mut ParseBuffer) -> Result<(String, String), String> {
    let typecode: String;
    let variable: String;
    skip_blanks(b);
    match parse_symbol(b) {
        Ok(t) => typecode = t,
        Err(e) => return Err(e)
    }
    skip_blanks(b);
    match parse_symbol(b) {
        Ok(v) => variable = v,
        Err(e) => return Err(e)
    }
    skip_blanks(b);
    match read_next_token(b) {
        Ok(Token::EndStatement) => {},
        Ok(_) => return Err(format!("Unexpected token ${}", b.bytes[b.i - 1] as char)),
        Err(e) => return Err(e)
    }
    Ok((typecode, variable))
}

fn register_floating(label: Label, typecode: String, variable: String, mut state: ParserState) -> Result<ParserState, String> {
    let typ: Constant;
    let var: Variable;
    match get_constant(&typecode, &state.program) {
        Some(t) => typ = t,
        None => return Err(format!("Type {} not found in constants", typecode))
    }
    match get_variable(&variable, &state) {
        Some(v) => var = v,
        None => return Err(format!("Variable {} not defined", variable))
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
    Ok(state)
}

fn parse_floating_stmt(b: &mut ParseBuffer, label: Label, mut state: ParserState) -> Result<ParserState, String> {
    match parse_floating(b) {
        Ok((typecode, variable)) => match register_floating(label, typecode, variable, state) {
            Ok(ns) => state = ns,
            Err(e) => return Err(e)
        },
        Err(e) => return Err(e)
    }
    state.program.n_stmt += 1;
    Ok(state)
}

fn parse_symbols_until(b: &mut ParseBuffer, end_token: Token) -> Result<Vec<String>, String> {
    let mut symbols = vec![];
    loop {
        skip_blanks(b);
        match read_next_token(b) {
            Ok(Token::OtherNotRead) => {
                match parse_symbol(b) {
                    Ok(s) => symbols.push(s),
                    Err(e) => return Err(e)
                }
            },
            Ok(t) => {
                if t == end_token {
                    break
                }
                else {
                    return Err(format!("Unexpected token ${}", b.bytes[b.i - 1] as char))
                }
            },
            Err(e) => return Err(e)
        }
    }
    Ok(symbols)
}

fn parse_symbols(b: &mut ParseBuffer) -> Result<Vec<String>, String> {
    return parse_symbols_until(b, Token::EndStatement);
}

fn parse_typed_symbols_until(b: &mut ParseBuffer, end_token: Token) -> Result<(String, Vec<String>), String> {
    let typecode: String;
    let symbols: Vec<String>;
    skip_blanks(b);
    match read_next_token(b) {
        Ok(Token::OtherNotRead) => {
            match parse_symbol(b) {
                Ok(s) => typecode = s,
                Err(e) => return Err(e) } },
        Ok(_) => return Err(format!("Unexpected token ${}", b.bytes[b.i - 1] as char)),
        Err(e) => return Err(e)
    }
    match parse_symbols_until(b, end_token) {
        Ok(ss) => symbols = ss,
        Err(e) => return Err(e)
    }
    Ok((typecode, symbols))
}

fn parse_typed_symbols(b: &mut ParseBuffer) -> Result<(String, Vec<String>), String> {
    return parse_typed_symbols_until(b, Token::EndStatement);
}

fn encode_typed_symbols(typecode: String, symbols: Vec<String>, state: &ParserState) -> Result<(Constant, Vec<Symbol>), String> {
    let typ: Constant;
    match get_constant(&typecode, &state.program) {
        Some(t) => typ = t,
        None => return Err(format!("Type {} not found in constants", typecode))
    }
    let mut syms = vec![];
    for sym in symbols {
        match get_constant(&sym, &state.program) {
            Some(c) => syms.push(c),
            None => {
                match get_variable(&sym, &state) {
                    Some(v) => {
                        if !state.scope.vartypes.contains_key(&v) {
                            return Err(format!("Variable {} must be assigned a type", sym))
                        }
                        syms.push(v)
                    },
                    None => return Err(format!("Variable or constant {} not defined", sym))
                }
            }
        }
    }
    Ok((typ, syms))
}

fn register_essential(label: Label, typecode: String, symbols: Vec<String>, mut state: ParserState) -> Result<ParserState, String> {
    match encode_typed_symbols(typecode, symbols, &state) {
        Ok((typ, syms)) => {
            state.scope.essentials.insert(label, TypedSymbols { typ: typ, syms: syms });
        },
        Err(e) => return Err(e)
    }
    Ok(state)
}

fn parse_essential_stmt(b: &mut ParseBuffer, label: Label, mut state: ParserState) -> Result<ParserState, String> {
    match parse_typed_symbols(b) {
        Ok((typecode, symbols)) => match register_essential(label, typecode, symbols, state) {
            Ok(ns) => state = ns,
            Err(e) => return Err(e)
        },
        Err(e) => return Err(e)
    }
    state.program.n_stmt += 1;
    Ok(state)
}

fn register_disjoint(variables: Vec<String>, mut state: ParserState) -> Result<ParserState, String> {
    let mut vars = vec![];
    for var in variables {
        match get_variable(&var, &state) {
            Some(v) => {
                if vars.contains(&v) {
                    return Err(format!("Variable {} appears more than once in a disjoint statement", var));
                }
                vars.push(v)
            },
            None => return Err(format!("Variable {} not defined", var))
        }
    }
    vars.sort();
    for (v1, v2) in vars.iter().tuple_combinations() {
        state.scope.disjoints.insert((*v1, *v2));
    }
    Ok(state)
}

fn parse_disjoint_stmt(b: &mut ParseBuffer, mut state: ParserState) -> Result<ParserState, String> {
    match parse_symbols(b) {
        Ok(variables) => match register_disjoint(variables, state) {
            Ok(ns) => state = ns,
            Err(e) => return Err(e)
        },
        Err(e) => return Err(e)
    }
    state.program.n_stmt += 1;
    Ok(state)
}

fn mandatory_variables(syms: &Vec<Symbol>, scope: &Scope) -> HashSet<Variable> {
    let mut mvars = HashSet::new();
    for s in syms.iter() {
        if scope.variables.contains(&s) {
            mvars.insert(*s);
        }
    }
    for e in scope.essentials.values() {
        for s in e.syms.iter() {
            if scope.variables.contains(&s) {
                mvars.insert(*s);
            }
        }
    }
    mvars
}

pub fn mandatory_hypotheses(mvars: &HashSet<Variable>, scope: &Scope) -> Vec<Label> {
    let mut mhyps = HashSet::new();
    for (label, f) in scope.floatings.iter() {
        if mvars.contains(&f.var) {
            mhyps.insert(*label);
        }
    }
    for label in scope.essentials.keys() {
        mhyps.insert(*label);
    }
    let mut sorted_mhyps: Vec<Label> = mhyps.iter().cloned().collect();
    sorted_mhyps.sort();
    sorted_mhyps
}

pub fn mandatory_disjoints(mvars: &HashSet<Variable>, scope: &Scope) -> HashSet<(Variable, Variable)> {
    let mut mdisjs = HashSet::new();
    for (v1, v2) in scope.disjoints.iter() {
        if mvars.contains(v1) && mvars.contains(v2) {
            mdisjs.insert((*v1, *v2));
        }
    }
    mdisjs
}

fn create_assertion(typecode: String, symbols: Vec<String>, state: &ParserState) -> Result<Assertion, String> {
    match encode_typed_symbols(typecode, symbols, state) {
        Ok((typ, syms)) => {
            let mvars = mandatory_variables(&syms, &state.scope);
            let mhyps = mandatory_hypotheses(&mvars, &state.scope);
            let mdisj = mandatory_disjoints(&mvars, &state.scope);
            return Ok(Assertion {
                ax: TypedSymbols { typ: typ, syms: syms },
                proof: None,
                scope: state.scope.clone(),
                mvars: mvars,
                mhyps: mhyps,
                mdisj: mdisj,
            });
        },
        Err(e) => return Err(e)
    }
}

fn parse_axiom_stmt(b: &mut ParseBuffer, label: Label, mut state: ParserState) -> Result<ParserState, String> {
    match parse_typed_symbols_until(b, Token::EndStatement) {
        Ok((typecode, symbols)) => match create_assertion(typecode, symbols, &state) {
            Ok(axiom) => { state.program.axioms.insert(label, axiom); },
            Err(e) => return Err(e) },
        Err(e) => return Err(e)
    }
    state.program.n_stmt += 1;
    Ok(state)
}

pub fn decode_proof_chars(chars: &String, labels: &Vec<Label>, mhyps: &Vec<Label>, state: &ParserState) -> Result<Proof, String> {
    let m = mhyps.len();
    let n = labels.len();
    let mut proof = vec![];
    let mut acc = 0;
    for c in chars.chars() {
        if c == '?' {
            proof.push(ProofStep::Unknown());
            continue
        }
        if c == 'Z' {
            proof.push(ProofStep::Save());
            continue
        }
        if c > 'T' {
            acc = 5 * acc + 20 * ((c as u32) - 84);
            continue
        }
        let i = (acc + ((c as u32) - 64)) as usize;
        if i <= m {
            match get_label_proof_step(mhyps[i - 1], state) {
                Ok(proofstep) => { proof.push(proofstep); acc = 0; continue },
                Err(e) => return Err(e) }
        }
        if i <= m + n {
            match get_label_proof_step(labels[i - m - 1], state) {
                Ok(proofstep) => { proof.push(proofstep); acc = 0; continue },
                Err(e) => return Err(e) }
        }
        proof.push(ProofStep::Load(i - m - n - 1));
        acc = 0;
    }
    Ok(proof)
}

fn parse_compressed_proof(b: &mut ParseBuffer, provable: &Assertion, state: &ParserState) -> Result<Proof, String> {
    let mut labels = vec![];
    let mut chars = "".to_string();
    match parse_symbol(b) {
        Ok(s) => if s != "(" { return Err(format!("Unexpected token {}", s)) },
        Err(e) => return Err(e)
    }
    loop {
        skip_blanks(b);
        match parse_label(b) {
            Ok(l) => {
                if l == "" { break }
                if !state.program.labels.contains_key(&l) {
                    return Err(format!("Label {} not defined.", l))
                }
                labels.push(state.program.labels[&l]);
                continue
            },
            Err(e) => return Err(e)
        }
    }
    match parse_symbol(b) {
        Ok(s) => if s != ")" { return Err(format!("Unexpected token {}", s)) },
        Err(e) => return Err(e)
    }
    loop {
        skip_blanks(b);
        match parse_label(b) {
            Ok(l) => {
                if l == "" { break }
                chars.push_str(l.as_str());
                continue
            },
            Err(e) => return Err(e)
        }
    }
    match read_next_token(b) {
        Ok(Token::EndStatement) => {},
        Ok(_) => return Err(format!("Unexpected token ${}", b.bytes[b.i - 1] as char)),
        Err(e) => return Err(e)
    }
    decode_proof_chars(&chars, &labels, &provable.mhyps, &state)
}

fn get_label_proof_step(label: Label, state: &ParserState) -> Result<ProofStep, String> {
    if state.scope.floatings.contains_key(&label) {
        return Ok(ProofStep::Floating(label))
    }
    if state.scope.essentials.contains_key(&label) {
        return Ok(ProofStep::Essential(label))
    }
    if state.program.axioms.contains_key(&label) {
        return Ok(ProofStep::Axiom(label))
    }
    if state.program.provables.contains_key(&label) {
        return Ok(ProofStep::Provable(label))
    }
    Err(format!("Label {} not found in floatings, essentials, axioms or provables.", label))
}

fn parse_uncompressed_proof(b: &mut ParseBuffer, state: &ParserState) -> Result<Proof, String> {
    let mut proof = vec![];
    loop {
        skip_blanks(b);
        match read_next_token(b) {
            Ok(Token::EndStatement) => break,
            Ok(Token::OtherNotRead) => {
                match parse_symbol(b) {
                    Ok(s) => {
                        if s == "?" {
                            proof.push(ProofStep::Unknown());
                            continue
                        }
                        if !state.program.labels.contains_key(&s) {
                            return Err(format!("Label {} not defined.", s));
                        }
                        let label = state.program.labels[&s];
                        match get_label_proof_step(label, state) {
                            Ok(proofstep) => { proof.push(proofstep); continue },
                            Err(e) => return Err(e) }
                    },
                    Err(e) => return Err(e) } },
            Ok(_) => return Err(format!("Unexpected token ${}", b.bytes[b.i - 1] as char)),
            Err(e) => return Err(e)
        }
    }
    Ok(proof)
}

fn parse_proof(b: &mut ParseBuffer, provable: &Assertion, state: &ParserState) -> Result<Proof, String> {
    skip_blanks(b);
    let start = b.i;
    match parse_symbol(b) {
        Ok(s) => {
            b.i = start;  // rewind
            if s == "(" {
                return parse_compressed_proof(b, provable, state)
            }
            else {
                return parse_uncompressed_proof(b, state)
            } },
        Err(e) => return Err(e)
    }
}

fn parse_provable_stmt(b: &mut ParseBuffer, label: Label, mut state: ParserState) -> Result<ParserState, String> {
    match parse_typed_symbols_until(b, Token::StartProof) {
        Ok((typecode, symbols)) => match create_assertion(typecode, symbols, &state) {
            Ok(mut provable) => match parse_proof(b, &provable, &state) {
                Ok(proof) => {
                    provable.proof = Some(proof);
                    state.program.provables.insert(label, provable); },
                Err(e) => return Err(e) },
            Err(e) => return Err(e) },
        Err(e) => return Err(e)
    }
    state.program.n_stmt += 1;
    Ok(state)
}

fn parse_labeled_stmt(b: &mut ParseBuffer, mut state: ParserState) -> Result<ParserState, String> {
    let label: Label;

    skip_blanks(b);
    require_another_byte!(b);
    match parse_label(b) {
        Ok(l) => match register_label(l, state) {
            Ok((ns, lab)) => { state = ns; label = lab },
            Err(e) => return Err(e)
        },
        Err(e) => return Err(e)
    }

    loop {
        skip_blanks(b);
        match read_next_token(b) {
            Ok(Token::StartFloating) => return parse_floating_stmt(b, label, state),
            Ok(Token::StartEssential) => return parse_essential_stmt(b, label, state),
            Ok(Token::StartAxiom) => return parse_axiom_stmt(b, label, state),
            Ok(Token::StartProvable) => return parse_provable_stmt(b, label, state),
            Ok(Token::OtherNotRead) => return Err(format!("Unexpected token {}", b.bytes[b.i] as char)),
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
        Ok(Token::StartDisjoint) => return parse_disjoint_stmt(b, state),
        Ok(Token::OtherNotRead) => {},
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
            Ok(Token::OtherNotRead) => {},
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
            Ok(Token::OtherNotRead) => {},
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
    println!("The source has {} statements; {} are $a and {} are $p.",
             state.program.n_stmt, state.program.axioms.len(), state.program.provables.len());
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
        i: 0,
    };
    println!("{} bytes", b.bytes.len());
    match parse_top_level(&mut b, state) {
        Ok(ns) => state = ns,
        Err(e) => return Err(e)
    }
    // println!("Constants: {:?}", state.program.constants.keys());
    println!("{} constants", state.program.constants.len());
    println!("{} variables", state.program.variables.len());
    println!("{} symbols", state.program.symbols.len());
    println!("{} labels", state.program.labels.len());
    println!("Program parsed in {:?}", now.elapsed());
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
