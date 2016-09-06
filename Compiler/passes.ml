(**
This module provides a framework to transform the initial AST to a simplified AST for the code generation.
It also allows to easily add other passes.
At the moment, the initial and simplified AST are really close. 
**) 
open Ast
open Tast

exception Error of string
exception Byte
module SMap = Map.Make(String)
let type_mappings = ref SMap.empty
let modifiers = ref SMap.empty

(* Transforms the simple types. Nothing changes *)
let compute_elem_type (t : Ast.elem_type_name) : Tast.elem_type_name = match t with
    | TEInt -> TEInt
    | TEUint -> TEInt
    | TEBytes ->  raise Byte
    | TEByte -> raise Byte
    | TEString -> TEString
    | TEAddress -> TEAddress
    | TEBool -> TEBool
    | TEFixed -> raise (Error ("type fixed not supported"))
    | TEUFixed -> raise (Error ("type ufixed not supported"))

(* Transforms the type *)
let rec compute_type (t : Ast.type_name) id : Tast.type_name = match t with
    | TIdent s -> TIdent s
    | TMapping (el_t, t_bis) -> TMapping (compute_elem_type el_t, compute_type t_bis id) 
    | TElem e -> let typ = (try TElem (compute_elem_type e) with
        | Byte -> TMapping (TEInt, TElem (TEInt))
        | s -> raise s) in type_mappings := SMap.add id typ (!type_mappings); typ

(* Transforms the visibility *)
let compute_visibility (v : Ast.visibility) : Tast.visibility = match v with
    | Public -> Public
    | Private -> Private
    | Internal -> Internal

(* Extracts the visibility specifiers from the list of possible infos about a Solidity function *)
let rec compute_visibility_infos (l : Ast.vis_or_loc_or_cst list) (accu : Tast.visibility) : Tast.visibility = match l with
    | [] -> accu
    | a::q -> (match a with 
            | VS v -> (match accu with
                    | VDefault -> compute_visibility_infos q (compute_visibility v)
                    | _ -> raise (Error ("Several visibility specifiers"))
                    )
            | _ -> compute_visibility_infos q accu
            )

(* Extracts the constant info from the list of possible infos about a Solidity function *)
let rec compute_constant_infos (l : Ast.vis_or_loc_or_cst list) (accu : bool) = match l with
    | [] -> accu
    | a::q -> (match a with
            | CST -> if accu then raise (Error ("several constant keywords")) else compute_constant_infos q true
            | _ -> compute_constant_infos q accu
            )
(* Transforms the location *)
let compute_location (v : Ast.location_spec) : Tast.location_spec = match v with
    | Memory -> Memory
    | Storage -> Storage

(* Extracts the storage location specifiers from the list of possible infos about a Solidity function *)
let rec compute_location_infos (l : Ast.vis_or_loc_or_cst list) (accu : Tast.location_spec) : Tast.location_spec = match l with 
    | [] -> accu
    | a::q -> (match a with
            | LS v -> (match accu with
                    | LDefault -> compute_location_infos q (compute_location v)
                    | _ -> raise (Error ("Several location specifiers"))
                    )
            | _ -> compute_location_infos q accu
            )

(* Binary operators are the same in both AST *)
let compute_binop (op : Ast.binop) : Tast.binop = match op with
    | OpLt -> OpLt
    | OpLe -> OpLe
    | OpGt -> OpGt
    | OpGe -> OpGe
    | OpEq -> OpEq
    | OpNeq -> OpNeq
    | OpPlus -> OpPlus
    | OpMinus -> OpMinus
    | OpMul -> OpMul
    | OpAnd -> OpAnd
    | OpOr -> OpOr

(* Expressions are the same in both AST *)
let rec compute_expression (e : Ast.expression) : Tast.expression = match e with
    | EInt s -> EInt s
    | EBool b -> EBool b
    | EStr s -> EStr s
    | EVar id -> EVar id
    | EFieldVar (e, id) -> EFieldVar (compute_expression e, id)
    | EArrayVar (id, el) -> EArrayVar (id, List.map compute_expression el)
    | EConditional (e1, e2, e3) -> EConditional (compute_expression e1, compute_expression e2, compute_expression e3)
    | ENot e -> ENot (compute_expression e)
    | EInc e -> EInc (compute_expression e)
    | EDec e -> EDec (compute_expression e)
    | EBinOp (op, e1, e2) -> EBinOp (compute_binop op, compute_expression e1, compute_expression e2)
    | EFunCall (id, el) -> EFunCall (id, List.map compute_expression el)
    | EFieldFunCall (e, id, el) -> EFieldFunCall (compute_expression e, id, List.map compute_expression el)

(* Expressions options are the same in both AST *)
let compute_expr_opt (oe : Ast.expression option) : Tast.expression option = match oe with
    | None -> None
    | Some e -> Some (compute_expression e)

(* Simplifies the variable definitions to extract visibility, constnat and location information *)
let compute_var_def (e : Ast.variable_def) : Tast.variable_def =
    { v_name = e.v_name; v_type = compute_type e.v_type e.v_name; v_visibility = compute_visibility_infos e.v_infos VDefault; v_is_const = compute_constant_infos e.v_infos false; v_location = compute_location_infos e.v_infos LDefault; v_expr = compute_expr_opt e.v_expr }

(* Calls compute_var_def on the list of variable definitions in a structure *)
let rec compute_var_defs (l : Ast.variable_def list) (accu : Tast.variable_def list) : Tast.variable_def list = match l with
    | [] -> accu
    | a::q -> compute_var_defs q ((compute_var_def a)::accu)

(* Simplifies the variable definitions in a structure *)
let compute_struct (s : Ast.struct_def) : Tast.struct_def  = 
    { s_name = s.s_name; s_vars = compute_var_defs s.s_vars [] }

(* Nothing changes for function parameters *)
let compute_param (p : Ast.type_name * Ast.ident) : Tast.type_name * Tast.ident = 
    (compute_type (fst p) (snd p), snd p)

(* Removes the option in visibility. If none was specified, we update it to default *)
let compute_opt_vis (ov : Ast.visibility option) : Tast.visibility = match ov with
    | None -> VDefault
    | Some v -> compute_visibility v

(* Replaces an option of parameter list by a parameter list to ease the code generation *)
let compute_option_paramslist (ol : Ast.param_list option) : (Tast.type_name * Tast.ident) list = match ol with
    | None -> []
    | Some l -> List.map compute_param l

(* Nothing chnages in assignments types *)
let compute_assign_op (op : Ast.assign_op) : Tast.assign_op = match op with
    | Assign -> Assign
    | AssignAdd -> AssignAdd
    | AssignSub -> AssignSub
    | AssignMul -> AssignMul

(* Adds the type of the assignment when a mapping is involved *)
let compute_varassign (va : Ast.var_assign) : Tast.var_assign = match va with
    | VAIdent (op, id, e) -> VAIdent (compute_assign_op op, id, compute_expression e)
    | VAField (op, e, id, e2) -> VAField (compute_assign_op op, compute_expression e, id, compute_expression e2)
    | VAIdentArray (op, id, el, e) -> VAIdentArray(compute_assign_op op, id, List.map compute_expression el, compute_expression e, try SMap.find id (!type_mappings) with | _ -> raise (Error id))
    | VAFieldArray (op, e1, id, el, e2) -> VAFieldArray(compute_assign_op op, compute_expression e1, id, List.map compute_expression el, compute_expression e2, SMap.find id (!type_mappings))

(* Transforms the statements.
If we have an if or an if/else, we add all the remaining instructions to the instruciton in the block to avoid merging control flows during code generation *)
let rec compute_statement (st_list : Ast.statement list) (s : Ast.statement) : Tast.statement = match s with
    | SIf (e, s) -> SIf (compute_expression e, compute_statement (if (st_list != []) then List.tl st_list else []) s, compute_statement_list st_list)
    | SIfElse (e, s1, s2) -> SIfElse (compute_expression e, compute_statement (if (st_list != []) then List.tl st_list else []) s1, compute_statement (if (st_list != []) then List.tl st_list else []) s2, compute_statement_list st_list)
    | SWhile (e, s) -> SWhile (compute_expression e, compute_statement_list s)
    | SBlock sl -> SBlock (compute_statement_list sl)
    | SReturn eo -> SReturn (compute_expr_opt eo)
    | SThrow -> SThrow
    | SExpr e -> SExpr (compute_expression e)
    | SVarDecl v -> SVarDecl (compute_var_def v)
    | SVarAssign va -> SVarAssign (compute_varassign va)

(* Transforms the list of statements *)
and compute_statement_list = function
    | [] -> []
    | a::q -> (compute_statement q a) :: (compute_statement_list q)

(* Collects all the modifiers specified in a function, retrieve the code for each of these modifiers, 
and concatene them. We only allow modifiers as decorators, whose code will thus be inserted at the beginning of the function *)
let rec collect_modifier_insns (lst : ident list) (accu : Tast.statement list) = match lst with
    | [] -> accu
    | a::q -> try (
        (SMap.find a (!modifiers)) @ (collect_modifier_insns q accu)
        ) with 
        | _ -> raise (Error (a ^" modifier unknown"))

(* Transforms function. Simplifies the different information, and appends insert the modifiers statements at the beginning of the function if there was any modifier *)
let compute_function (f : Ast.function_def) : Tast.function_def =
    { func_name = f.func_name; func_params = List.map compute_param f.func_params; func_vis = compute_visibility_infos f.func_infos VDefault; func_ret_params = compute_option_paramslist f.func_ret_params; func_insns = List.append (collect_modifier_insns f.func_mods []) (compute_statement_list f.func_insns); func_mods = f.func_mods }

(* Transforms modifiers *)
let compute_modifier (m : Ast.modifier_def) : Tast.modifier_def = 
    { mod_name = m.mod_name; mod_params = List.map compute_param m.mod_params; mod_insns = compute_statement_list m.mod_insns}

(* Nothing changes for enums *)
let compute_enum (e : Ast.enum_def) : Tast.enum_def = {enum_name = e.enum_name; enum_vals = e.enum_vals}

(* Extracts the state variables from the list of possible parts of a contract, that can come in any order *)
let rec compute_ctr_vars (l : Ast.contract_part list) (accu : Tast.variable_def list) : Tast.variable_def list = match l with 
    | [] -> accu
    | a::q -> (match a with
        | VariableDecl v ->  compute_ctr_vars q ((compute_var_def v)::accu)
        | _ -> compute_ctr_vars q accu
        )

(* Extracts the structures from the list of possible parts of a contract, that can come in any order *)
let rec compute_ctr_structs (l : Ast.contract_part list) (accu : Tast.struct_def list) : Tast.struct_def list = match l with
    | [] -> accu
    | a::q -> (match a with 
        | StructDef s -> compute_ctr_structs q ((compute_struct s)::accu)
        | _ -> compute_ctr_structs q accu 
        )

(* Extracts the enumerations from the list of possible parts of a contract, that can come in any order *)
let rec compute_ctr_enums (l : Ast.contract_part list) (accu : Tast.enum_def list) : Tast.enum_def list = match l with
    | [] -> accu
    | a::q -> (match a with
        | EnumDef e -> compute_ctr_enums q ((compute_enum e)::accu)
        | _ -> compute_ctr_enums q accu
        )

(* Extracts the functions from the list of possible parts of a contract, that can come in any order *)
let rec compute_ctr_funs (l : Ast.contract_part list) (accu : Tast.function_def list) : Tast.function_def list = match l with
    | [] -> accu
    | a::q -> (match a with
        | FunctionDef f -> compute_ctr_funs q ((compute_function f)::accu)
        | _ -> compute_ctr_funs q accu
        )

(* Extracts the anonymous function from the list of possible parts of a contract, that can come in any order *)
let rec compute_ctr_anonymous (l : Ast.contract_part list) (accu : Tast.statement list) : (Tast.statement list) = match l with
    | [] -> accu
    | a::q -> (match a with
        | AnonymousFun sl -> (if accu != [] then raise (Error ("Several anonymous functions")) else compute_ctr_anonymous q (compute_statement_list sl))
        | _ -> compute_ctr_anonymous q accu
        ) 

(* Types the annotation. At the moment, we only target preservation annotation, but this would allow to identify and try to prove other types of properties *)
let compute_annot_type (e : ident) = match e with
    | "preservation" -> Preservation
    | s -> raise (Error (s ^ " is not a supported annotation type"))

(* When we have an evaluation function for an annotation in the mapping, we replace the access in the pair (key, value) from an element of the mapping
by a call to "fst" or "snd" in Coq *)
let rec replace_key_value ( e : Ast.expression) : Ast.expression = match e with
   | EVar id when id = "key" -> EFunCall ("fst", [EVar "x"])
   | EVar id when id = "value" -> EFunCall ("snd", [EVar "x"])
   | e -> e

(* Transforms an annotation. Distinguishes between the case where we have an evaluation function specified for a mapping, and not.
In the first case, we also check that the evaluation function is defined as "fun(key, value) = expression", where expression is user-defined. *)
let compute_annot (a : Ast.annotation_def) : Tast.annotation_def = 
   match a.an_count_elem with
   | None -> { an_type = compute_annot_type a.an_type; an_var = a.an_var; an_funs = a.an_funs; an_count_elem = None }
   | Some e -> if ((a.an_fname <> "fun") || (a.an_key <> "key") || (a.an_value <> "value"))  then
	raise (Error ("annotation function should be \"fun(key, value) = expression\"")) else
   { an_type = compute_annot_type a.an_type; an_var = a.an_var; an_funs = a.an_funs; an_count_elem = Some(compute_expression (replace_key_value e)) } 

(* Extracts the annotations from the list of possible parts of a contract, that can come in any order *)
let rec compute_ctr_annotations (l : Ast.contract_part list) (accu : Tast.annotation_def list) : (Tast.annotation_def list) = match l with
    | [] -> List.rev accu
    | a::q -> (match a with
        | Annotation e -> compute_ctr_annotations q ((compute_annot e)::accu)
        | _ -> compute_ctr_annotations q accu
        )

(* Extracts the modifier definitions from the list of possible parts of a contract, that can come in any order *)
let rec compute_ctr_modifiers (l : Ast.contract_part list) (accu : Tast.modifier_def list) : (Tast.modifier_def list) = match l with
    | [] -> List.rev accu
    | a::q -> (match a with
        | ModifierDef e -> let tmod = compute_modifier e in begin
            modifiers := SMap.add tmod.mod_name tmod.mod_insns (!modifiers); 
             compute_ctr_modifiers q ((tmod)::accu) end
        | _ -> compute_ctr_modifiers q accu
        )

(* Transforms a whole contract by seperating the different possible parts (state variables, structures, enums, functions, anonymous function and modifiers)
by calling the functions defined previously *)
let compute_contract (c_def : Ast.contract_def) : Tast.contract_def =
    let ctr_vars = compute_ctr_vars c_def.c_parts [] in
    let ctr_structs = compute_ctr_structs c_def.c_parts [] in
    let ctr_modifiers = compute_ctr_modifiers c_def.c_parts [] in
    { c_name = c_def.c_name; c_vars = ctr_vars; c_structs = ctr_structs; c_funs = compute_ctr_funs c_def.c_parts []; c_anonymousfun = compute_ctr_anonymous c_def.c_parts []; c_annotations = compute_ctr_annotations c_def.c_parts [];
    c_modifiers = ctr_modifiers; c_enums = compute_ctr_enums c_def.c_parts []} 

(* The entry point of this module.
It allows to transform a list of contracts defined in Solidity.
Nevertheless, the code generation only allows to have one contract in the Solidity code. 
Thus file.f_contracts will always be a list with one element *)
let type_file (file : Ast.file) : Tast.file = 
    { f_contracts = List.map compute_contract file.f_contracts }
