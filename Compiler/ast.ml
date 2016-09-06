type ident = string

type file = { f_contracts : contract_def list }

and contract_def = { c_name : ident ; c_parts : contract_part list }

and contract_part = 
| FunctionDef of function_def
| EnumDef of enum_def
| StructDef of struct_def
| VariableDecl of variable_def
| EventDef of event_def
| AnonymousFun of statement list
| Annotation of annotation_def
| ModifierDef of modifier_def

and enum_def = {enum_name : ident; enum_vals : ident list}

and visibility =
| Public
| Private
| Internal

and location_spec = 
| Memory
| Storage
    
and annotation_def = { an_type : ident; an_var: ident; an_funs : ident list; an_fname : ident; an_key : ident; an_value : ident; an_count_elem : expression option}

and event_def = { ev_name : ident; ev_params : param_list option }

and variable_def = { v_name : ident; v_type : type_name; v_infos : vis_or_loc_or_cst list; v_expr : expression option}
 
and vis_or_loc_or_cst = 
| VS of visibility
| LS of location_spec
| CST

and struct_def = { s_name : ident; s_vars : variable_def list }

and function_def = { func_name : ident; func_params : param_list; func_infos : vis_or_loc_or_cst list; func_ret_params : param_list option; func_insns : statement list; func_mods : ident list }

and modifier_def = { mod_name : ident; mod_params : param_list; mod_insns : statement list }

and param_list = (type_name * ident) list

and type_name = 
| TIdent of ident
| TMapping of elem_type_name * type_name
| TElem of elem_type_name

and elem_type_name =
| TEInt
| TEUint
| TEBytes
| TEByte
| TEString
| TEAddress
| TEBool
| TEFixed
| TEUFixed

and statement =
| SIf of expression * statement
| SIfElse of expression * statement * statement
| SWhile of expression * statement list
| SBlock of statement list
| SReturn of expression option
| SThrow
| SExpr of expression
| SVarDecl of variable_def
| SVarAssign of var_assign

and var_assign =
| VAIdent of assign_op * ident * expression
| VAField of assign_op * expression * ident * expression
| VAIdentArray of assign_op * ident * expression list * expression
| VAFieldArray of assign_op * expression * ident * expression list * expression

and assign_op = 
| Assign
| AssignAdd
| AssignSub
| AssignMul

and expression =
| EInt of int
| EBool of bool
| EStr of string
| EVar of ident
| EFieldVar of expression * ident
| EArrayVar of ident * expression list
| EConditional of expression * expression * expression
| ENot of expression
| EInc of expression
| EDec of expression
| EBinOp of binop * expression * expression
| EFunCall of ident * expression list
| EFieldFunCall of expression * ident * expression list


and binop = 
| OpLt
| OpLe
| OpGt
| OpGe
| OpEq
| OpNeq
| OpPlus
| OpMinus
| OpMul
| OpAnd
| OpOr
