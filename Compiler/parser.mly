%{
    open Format
    open Lexer
    open Tokens
    open Ast
%}

/* Entrypoint */
%start file

/* Type returned */
%type <Ast.file> file

%%

file:
     c_def = contract_definition; EOF { { f_contracts = [c_def] } }
;

contract_definition:
    Contract id = Ident LBrace cp = contract_part* RBrace { { c_name = id; 
    c_parts = cp } }
    ;

contract_part:
| e = function_def { FunctionDef e }
| e = enum_def { EnumDef e}
| e = struct_def   { StructDef e }
| e = variable_decl { VariableDecl e }
| e = event_def    { EventDef e }
| e = modifier_def { ModifierDef e } 
| Function; LParen; RParen; b = block_or_empty { AnonymousFun b }
| Atmark;  e = annotation_def { Annotation e }
;

enum_def:
Enum; id = Ident; LBrace ; vals = separated_list(Comma, Ident); RBrace; { { enum_name = id; enum_vals = vals} }

annotation_def:
   | t = Ident; LParen; id = Ident; RParen { {an_type = t; an_var = id; an_funs = []; an_fname = ""; an_key = ""; an_value = ""; an_count_elem = None } }
   | t = Ident; LParen; id = Ident; Comma; f = Ident; LParen; key = Ident; Comma; value = Ident; RParen; Assign; e = expression;  RParen { { an_type = t; an_var = id; an_funs = []; an_fname = f; an_key = key; an_value = value; an_count_elem = Some(e) } } 



visibility_specifier:
| Public { Public }
| Private { Private }
| Internal { Internal }
;

location_specifier:
| Memory { Memory }
| Storage { Storage }

event_def:
    Event; id = Ident; p = params_list?; Anonymous? ; Semicolon; { { ev_name = id; ev_params = p } }
;    

%inline rule0:
| x = visibility_specifier  { VS x }
| x = location_specifier    { LS x }
| Const                     { CST }
;

variable_decl:
    t = type_name; infos_list = rule0*; id = Ident; e = option(preceded(Assign, expression)); Semicolon; { { v_name = id; v_type = t; v_infos = infos_list; v_expr = e } }
;


struct_def:
     Struct; id = Ident; LBrace; l = list(variable_decl); RBrace { { s_name = id; s_vars = l } }
;

function_def:
    Function; id = Ident; p = params_list; mods = list(Ident); x = rule0*; ret_par = option(preceded(Returns, params_list)); e = block_or_empty; { { func_name = id; func_params = p; func_infos = x; func_ret_params = ret_par; func_insns = e; func_mods = mods } }
;

modifier_def:
    Modifier; id=Ident; p=params_list; LBrace; sl = list(statement); Underscore; RBrace; { {mod_name = id; mod_params = p; mod_insns = sl } }
 ;

block_or_empty:
| b = block { b }
| Semicolon { [] }
;

parameter:
    t = type_name; Indexed?; id = Ident { (t, id) }
;

%inline params_list:
    | LParen; l = separated_list(Comma, parameter); RParen { l }
    | LParen; t = type_name; RParen { [(t, "Returned_result")] }   
;

type_name:
| e = elementary_type_name { TElem (e) }
| m = mapping { m }
| id = Ident { TIdent(id) }
;

elementary_type_name:
| Int { TEInt }
| UInt { TEUint }
| Bytes { TEBytes }
| Byte { TEByte }
| String { TEString }
| Address { TEAddress }
| Bool { TEBool }
| Fixed { TEFixed }
| UFixed { TEUFixed }
;

mapping:
    Mapping; LParen; first = elementary_type_name; Arrow; snd = type_name; RParen { TMapping(first, snd) }
 ;
 
block:
    LBrace; s = statement*; RBrace { s }
;

statement:
| If; LParen; e = expression; RParen; s = statement { SIf (e, s) } %prec If
| If; LParen; e = expression; RParen; s = statement; Else; s2 = statement { SIfElse(e, s, s2) }
| While; LParen; e = expression; RParen; LBrace; s = statement*; RBrace { SWhile(e, s) }
| s = block { SBlock(s) }
| Return; e = expression?; Semicolon { SReturn (e) }
| Throw; Semicolon { SThrow }
| e = expression; Semicolon { SExpr e }
| v = var_assign; Semicolon { SVarAssign v }
| d = variable_decl { SVarDecl d }
;

var_assign:
| id = Ident; op = assign_op; e = expression;  { VAIdent(op, id, e) }
| e = expression; Period; id = Ident; op = assign_op; e2 = expression;  { VAField(op, e, id, e2) }
| id = Ident; exp = nonempty_list(delimited(LBrack, expression, RBrack)); op = assign_op; e = expression;  { VAIdentArray(op, id, exp, e) }
| e = expression; Period; id = Ident; exp = nonempty_list(delimited(LBrack, expression, RBrack)); op = assign_op; res = expression;  { VAFieldArray(op, e, id, exp, res) }
;

%inline assign_op:
| Assign { Assign }
| AssignAdd { AssignAdd }
| AssignSub { AssignSub }
| AssignMul { AssignMul }
;

expression:
| i = CInt { EInt i }
| Minus; i = CInt { EInt (-i) }
| True { EBool (true) }
| False { EBool (false) }
| s = StringLiteral { EStr s }
| id = Ident { EVar id }
| e = expression; Period; id = Ident { EFieldVar(e, id) }
| id = Ident; par = nonempty_list(delimited(LBrack, expression, RBrack)) { EArrayVar (id, par) } 
| e1 = expression; Conditional; e2 = expression; Colon; e3 = expression { EConditional(e1, e2, e3) } %prec Conditional
| Not; e = expression { ENot e }
%prec Not
| e = expression; Inc { EInc e }
| e = expression; Dec { EDec e }
| e1 = expression; op = binop; e2 = expression { EBinOp(op, e1, e2) }
| id = Ident; LParen; l = separated_list(Comma, expression); RParen { EFunCall(id, l) }
| e = expression; Period; id = Ident; LParen; l = separated_list(Comma, expression); RParen { EFieldFunCall (e, id, l) }
;

%inline binop:
| Lt { OpLt }
| Le { OpLe }
| Gt { OpGt }
| Ge { OpGe }
| Equal { OpEq }
| NotEqual { OpNeq }
| Plus { OpPlus }
| Minus { OpMinus }
| Mul { OpMul }
| And { OpAnd }
| Or { OpOr}
;
