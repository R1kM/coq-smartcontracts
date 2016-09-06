open Format
open Lexing
open Passes 
open Codegen

let parse_only = ref false
let type_only = ref false

let filename = ref ""

let usage = "usage: solidity-coq [options] file.sol"

let set_var v s = v:=s

let options = ["--parse-only", Arg.Set parse_only, "Stops after parsing the input file";
               "--type-only", Arg.Set type_only, "Stops after typing the input file"]

let error_loc pos = 
    let line = pos.pos_lnum in
    let col = pos.pos_cnum-pos.pos_bol + 1 in
    eprintf "File \"%s\", line %d, characters %d-%d:\n" !filename line (col-1) col

let localisation2 (pos1, pos2) = 
    let l = pos1.pos_lnum in
    let c1 = pos1.pos_cnum - pos1.pos_bol + 1 in
    let c2 = pos2.pos_cnum - pos2.pos_bol + 1 in
    eprintf "File \"%s\", line %d, characters %d-%d:\n" !filename l c1 c2

let print_in_file ~file p = 
    let c = open_out file in
    let fmt = formatter_of_out_channel c in
    fprintf fmt "%s" p;
    pp_print_flush fmt ();
    close_out c

let () = 
    Arg.parse options (set_var filename) usage;
    
    if !filename = "" then
        (eprintf "No input file\n@?";
         exit 2);

    if not (Filename.check_suffix !filename ".sol") then (
        eprintf "Files must have the .sol extension\n@?";
        Arg.usage options usage;
        exit 2);

    let f = open_in !filename in
    let buf = Lexing.from_channel f in
    let basename = Filename.chop_suffix (!filename) ".sol" in

    try
        let p = Parser.file Lexer.token buf in
        close_in f;

        if not !parse_only then
        let p = Passes.type_file p in ();

        if not !type_only then
        let prog = Codegen.codegen p in
        print_in_file (basename ^".v") prog;
    with
        |Lexer.LexingError s ->
        error_loc (Lexing.lexeme_start_p buf);
        eprintf "%s\n@?" s;
        exit 1;
        |Parser.Error ->
        error_loc (Lexing.lexeme_start_p buf);
        eprintf "Syntax error\n@?";
        exit 1;

