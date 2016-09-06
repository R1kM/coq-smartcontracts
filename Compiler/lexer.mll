(* Lexer for solidity-coq *)

{
    open Lexing
    open Tokens 

    exception LexingError of string

    let keywords = [
        "_", Underscore;
        "anonymous", Anonymous;
        "assembly", Assembly;
        "break", Break;
        "constant", Const;
        "continue", Continue;
        "contract", Contract;
        "default", Default;
        "delete", Delete;
        "do", Do;
        "else", Else;
        "enum", Enum;
        "event", Event;
        "external", External;
        "false", False;
        "for", For;
        "function", Function;
        "if", If;
        "in", In;
        "indexed", Indexed;
        "internal", Internal;
        "import", Import;
        "is", Is;
        "library", Library;
        "mapping", Mapping;
        "memory", Memory;
        "modifier", Modifier;
        "new", New;
        "null", Null;
        "public", Public;
        "private", Private;
        "return", Return;
        "returns", Returns;
        "storage", Storage;
        "struct", Struct;
        "throw", Throw;
        "true", True;
        "var", Var;
        "while", While;
    ]

    let subdenominations = [
        "wei", SubWei;
        "szabo", SubSzabo;
        "finney", SubFinney;
        "ether", SubEther;
        "seconds", SubSeconds;
        "minutes", SubMinute;
        "hours", SubHour;
        "days", SubDays;
        "weeks", SubWeek;
        "years", SubYear;
        "after", After;
    ]

    let types = [
        "int", Int;
        "uint", UInt;
        "bytes", Bytes;
        "byte", Byte;
        "string", String;
        "address", Address;
        "bool", Bool;
        "fixed", Fixed;
        "ufixed", UFixed;
     ]
    
    let unsupported = ["after"; "break"; "continue"; "default"; "delete"; "do"; "external"; "for"; "import"; "in";  "is"; "library"; "new"; "null"; "days"; "ether"; "finney"; "hours"; "minutes"; "seconds"; "szabo"; "weeks"; "wei"; "years"; "var"]

    let newline lexbuf = 
        let pos = lexbuf.lex_curr_p in
        lexbuf.lex_curr_p <- {
            pos with pos_lnum = pos.pos_lnum + 1;
            pos_bol = pos.pos_cnum
        }

    let idOrKeyword s =
        try List.assoc s keywords with _ -> try List.assoc s subdenominations with | _ -> try List.assoc s types with | _ -> Ident s

    let idOrKeyword_unsupported s =
        if List.mem s unsupported then raise (LexingError (s ^ " keyword not supported")) else idOrKeyword s

}

    let digit = [ '0' - '9' ]
    let lowercaseLetter = [ 'a' - 'z' ]
    let uppercaseLetter = [ 'A' - 'Z' ]
    let alpha = lowercaseLetter | uppercaseLetter
    let identStart = '_' | '$' | alpha
    let ident = identStart (identStart | digit)*
    let hexa_digit = ['0'-'9' 'a'-'f' 'A'-'F']
    let integer = '0' | ['1'-'9'] digit* | "0x" hexa_digit+
    
    let car = digit | alpha  | ' ' | '!' | '#' | '$' | '%' | '&' | ''' | '('
    | ')' | '*' | '+' | '-' | ',' | '.' | '/' | ':' | ';' | '<' | '=' | '>' 
    | '?' | '@' | '[' | ']' | '^' | '_' | '`' | '{' | '|' | '}' | '~' 
    | "\\\\" | "\\\"" | "\\n" | "\\t"
    let space = [' ' '\t']


rule token = parse 
    | '\n'                      { newline lexbuf; token lexbuf }
    | "int" digit+              { Int }
    | "uint" digit+             { UInt }
    | "bytes" digit+            { Bytes }
    | "fixed" digit+ "x" digit+ { Fixed }
    | "ufixed" digit+ "x" digit+ { UFixed }
    | (ident as id)             { idOrKeyword_unsupported id }
    | space+                    { token lexbuf }
    | "/*"                      { long_comment lexbuf; token lexbuf }
    | "//"                      { short_comment lexbuf; token lexbuf }
    | integer as n              { CInt (int_of_string n) }
    | '@'                       { Atmark }
    | "\""                      { StringLiteral(strval_double "" lexbuf) }
    | "\'"                      { StringLiteral(strval_simple "" lexbuf) }
    | "<"                       { Lt }
    | "<="                      { Le }
    | "<<"                      { raise ( LexingError ("character << not supported")) }
    | "<<="                     { raise ( LexingError ("character <<= not supported")) }
    | ">"                       { Gt }
    | ">="                      { Ge }
    | ">>"                      { raise (LexingError ("character >> not supported")) }
    | ">>="                     { raise (LexingError ("character >>= not supported")) }
    | ">>>"                     { raise (LexingError ("character >>> not supported")) }
    | ">>>="                    { raise (LexingError ("character >>>= not supported")) }
    | "="                       { Assign }
    | "=="                      { Equal }
    | "=>"                      { Arrow }
    | "!"                       { Not }
    | "!="                      { NotEqual }
    | "+"                       { Plus }
    | "++"                      { Inc }
    | "+="                      { AssignAdd }
    | "-"                       { Minus }
    | "--"                      { Dec }
    | "-="                      { AssignSub }
    | "*"                       { Mul }
    | "**"                      { raise (LexingError ("character ** not supported")) }
    | "*="                      { AssignMul }
    | "%"                       { raise (LexingError ("character % not supported")) }
    | "%="                      { raise (LexingError ("character %= not supported")) }
    | "/"                       { raise (LexingError ("division not supported")) }
    | "/="                      { raise (LexingError ("division not supported")) }
    | "&"                       { raise (LexingError ("BitAnd not supported")) } 
    | "&&"                      { And }
    | "&="                      { raise (LexingError ("Bit operations not supported")) }
    | "|"                       { raise (LexingError ("Bit operations not supported")) }
    | "|="                      { raise (LexingError ("Bit operations not supported")) }
    | "||"                      { Or }
    | "^"                       { raise ( LexingError ("Bit operations not supported")) }
    | "^="                      { raise ( LexingError ("Bit operations not supported")) }
    | "."                       { Period }
    | ":"                       { Colon }
    | ";"                       { Semicolon }
    | ","                       { Comma }
    | "("                       { LParen }
    | ")"                       { RParen }
    | "["                       { LBrack }
    | "]"                       { RBrack }
    | "{"                       { LBrace }
    | "}"                       { RBrace }
    | "?"                       { Conditional }
    | "~"                       { raise (LexingError ("Bit operations not supported")) }
    | eof                       { EOF }
    | _ as c                    { raise (LexingError ("illegal character : " ^ String.make 1 c)) }

and strval_simple s = parse
    | "\'"              { s }
    | "\\\\"            { strval_simple (s ^"\\") lexbuf }
    | "\\\""            { strval_simple (s ^"\"") lexbuf }
    | "\\n"             { strval_simple (s ^"\n") lexbuf }
    | "\\t"             { strval_simple (s ^"\t") lexbuf }
    | "\\"              { raise (LexingError "Invalid Escape Sequence") }  
    | (car as c)        { strval_simple (s ^c) lexbuf }
    | eof               { raise (LexingError "Unfinished string") }
    | _                 { raise (LexingError "Invalid string") }

and strval_double s = parse
    | "\""              { s }
    | "\\\\"            { strval_double (s ^"\\") lexbuf }
    | "\\\""            { strval_double (s ^"\"") lexbuf }
    | "\\n"             { strval_double (s ^"\n") lexbuf }
    | "\\t"             { strval_double (s ^"\t") lexbuf }
    | "\\"              { raise (LexingError "Invalid Escape Sequence") }  
    | (car as c)        { strval_double (s ^c) lexbuf }
    | eof               { raise (LexingError "Unfinished string") }
    | _                 { raise (LexingError "Invalid string") }

and short_comment = parse  
    | '\n'              { newline lexbuf }
    | _                 { short_comment lexbuf }
    | eof               {}
    
and long_comment = parse
    | "*/"              {}
    | _                 { long_comment lexbuf }
    | eof               { raise (LexingError "Unclosed comment") }    
