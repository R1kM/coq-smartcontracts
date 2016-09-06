type ident = string

type file = { f_contracts : contract_def list }

and contract_def = { c_name : ident; c_vars : variable_def list; c_structs : struct_def list; c_funs : function_def list; c_anonymousfun : statement list; c_annotations : annotation_def list; c_modifiers : modifier_def list; c_enums : enum_def list }

and enum_def = { enum_name : ident; enum_vals : ident list}

and visibility = 
| VDefault
| Public
| Private
| Internal

and location_spec = 
| Memory
| Storage
| LDefault

and annotation_def = { an_type : annotation_type; an_var : ident; an_funs : ident list; an_count_elem : expression option}

and annotation_type = 
| Preservation

and variable_def = { v_name : ident; v_type : type_name; v_visibility : visibility; v_is_const : bool; v_location : location_spec; v_expr : expression option }

and struct_def = { s_name: ident; s_vars : variable_def list }
 
and function_def = { func_name : ident; func_params : (type_name * ident) list; func_vis : visibility; func_ret_params : (type_name * ident) list; func_insns : statement list; func_mods : ident list }

and modifier_def = { mod_name : ident; mod_params : (type_name * ident) list; mod_insns : statement list}

and type_name = 
| TIdent of ident
| TMapping of elem_type_name * type_name
| TElem of elem_type_name

and elem_type_name = 
| TEInt
| TEString
| TEAddress
| TEBool

and statement =
| SIf of expression * statement * statement list
| SIfElse of expression * statement * statement * statement list
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
| VAIdentArray of assign_op * ident * expression list * expression * type_name
| VAFieldArray of assign_op * expression * ident * expression list * expression * type_name

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

