(** This file generates coq code directly from the modified AST 
This code does not support the generation of several contracts, the whole code should consist of one Solidity contract
**)

open Tast
open Lemmas
exception Error of string

(* Used to keep track of required module in Coq *)
let required_modules = ref ["Arith"; "Nat"; "OrderedTypeEx"; "Coq.FSets.FMapList"; "BinInt"; "BinIntDef"]
let open_string = ref false
module VSet = Set.Make(String)

(* Keeps track of all state variables of the current contract *)
let state_vars = ref VSet.empty
let state_list = ref ["Unused"]

(* Names of functionns present reachable in the file to avoid generating events. Events should perhaps be removed in passes *)
let fun_names = ref ["()"; "fst"; "snd"; "send"]

(* Counter to generate unique auxiliary functions to model loops *)
let count_while = ref 0
(* The following references are used to store the auxiliary functions for loops, and the structures for passing and getting values from these functions, 
in order to generate them before any other function to avoid dependency issues *)
let while_structs = ref ""
let while_functions = ref ""

(* Helper to indicate that a Coq module is required *)
let add_required m = 
    if not (List.mem m (!required_modules)) then required_modules := m::(!required_modules)

(* Print the list of names of state variables *)
let rec print_state_vars = function
    | [] -> ""
    | a::q -> " "^a^(print_state_vars q)

(* Generates the type of a Solidity mapping in Coq, to declare a variable *)
let rec generate_mapping (e : Tast.elem_type_name) (t : Tast.type_name) = (match e with
    | TEInt | TEAddress -> "IntMap.t (" ^ (generate_type t) ^ ")"
    | TEString -> raise (Error ("string as map keys not supported")) 
    | TEBool -> raise (Error ("bool as map keys not supported"))
    )
    
(* Generates elementary types in Coq *)
and generate_elem_type = function
    | TEInt -> "Z"
    | TEString -> add_required "String"; "string"
    | TEAddress -> "Z"
    | TEBool -> "bool"

(* Generates a type in Coq *)
and generate_type (t : Tast.type_name) = match t with
    | TIdent id -> id
    | TElem e -> generate_elem_type e
    | TMapping (e, t) -> generate_mapping e t

(* Creates a default value for a mapping. Default value means that the mapping is empty *)
let rec init_mapping (e : Tast.elem_type_name) (t : Tast.type_name) = (match e with
    | TEInt | TEAddress -> "IntMap.empty (" ^ (generate_type t) ^ ")"
    | TEString -> raise (Error ("string as map keys not supported")) 
    | TEBool -> raise (Error ("bool as map keys not supported"))
    )

(* Generates a list of expressions *)
let rec generate_expression_list name = function
    | [] -> ""
    | a::q -> " (" ^ (generate_expression a name) ^ ")" ^ (generate_expression_list name q)

(* Generates expressions for the AST.
For a function call, we decrease the amount of gas before passing the new gas value, all the state variables, 
the ether balance of all accounts, the message from the sender, and finally all the parameters of the function. **)
and generate_expression (e : Tast.expression) name = match e with
    | EInt i -> string_of_int i 
    | EBool b -> string_of_bool b 
    | EStr s -> add_required "String"; open_string := true; "\"" ^s ^ "\"" 
    | EVar id -> id 
    | EFieldVar (e, id) -> (match e with
        | EVar ("msg") -> if (id = "sender") then "(sender msg)" else 
            if (id = "value") then "(value msg)" else raise (Error ("only msg.sender, msg.value and msg.gas supported for msg object")) 
        | _ -> raise (Error "EFieldVar not supported")) (* "(" ^ id ^ " " ^ (generate_expression e) ^ ")" ) *)
    | EArrayVar (id, el) -> "(get_"^id^ " " ^ id ^" " ^(generate_expression_list name el) ^")"
    | EConditional (e1, e2, e3) -> "if ("^(generate_expression e1 name) ^ ") then (" ^ (generate_expression e2 name) ^")\n else ("^(generate_expression e3 name) ^ ")\n" 
    | ENot e -> "( xorb  " ^ (generate_expression e name) ^" true)" 
    | EInc e -> raise (Error "Inc expression not supported yet") 
    | EDec e -> raise (Error "Dec expression not supported yet")
    | EBinOp (op, e1, e2) -> (match op with
        | OpLt -> "( ltb " ^ (generate_expression e1 name) ^ " "^ (generate_expression e2 name) ^")"
        | OpLe -> "( leb " ^ (generate_expression e1 name) ^ " "^ (generate_expression e2 name) ^")"
        | OpGt -> "( leb " ^ (generate_expression e2 name) ^ " "^ (generate_expression e1 name) ^")"
        | OpGe -> "( ltb " ^ (generate_expression e2 name) ^ " "^ (generate_expression e1 name) ^")"
        | OpEq -> "( eqb " ^ (generate_expression e1 name) ^ " "^ (generate_expression e2 name) ^ ")"
        | OpNeq -> "( xorb ( eqb " ^ (generate_expression e1 name) ^ " "^ (generate_expression e2 name) ^") true )"
        | OpPlus -> "(" ^ (generate_expression e1 name) ^ " + " ^ (generate_expression e2 name) ^ ")"
        | OpMinus -> "(" ^ (generate_expression e1 name) ^ " - " ^ (generate_expression e2 name) ^ ")"
        | OpMul -> "(" ^ (generate_expression e1 name) ^ " * " ^ (generate_expression e2 name) ^ ")"
        | OpAnd -> "( andb " ^ (generate_expression e1 name) ^ " " ^ (generate_expression e2 name) ^ ")"
        | OpOr -> "( orb " ^ (generate_expression e1 name) ^ " " ^ (generate_expression e2 name) ^ ")"
        )        
    | EFunCall (id, el) -> if (List.mem id (!fun_names)) then "let new_gas := (Nat.pred new_gas) in\n (" ^ id ^ " new_gas (create_"^name ^ (print_state_vars (List.tl(List.rev((!state_list))))) ^ ") new_ether msg" ^ (generate_expression_list name el) ^ ")" else ""
    | EFieldFunCall (e, id, el) -> raise (Error "FieldFunCall expression not supported yet")

(* Helper to generate expressions when an Option structure is involved *)
let generate_expression_opt ( eo : Tast.expression option) name =
    match eo with
    | None -> ""
    | Some e -> " := " ^ (generate_expression e name)

(* Declares a field of a structure. Used recursively to declare a structure *)
let generate_struct_var (v : Tast.variable_def) name =
    v.v_name ^ ": " ^ generate_type v.v_type ^ generate_expression_opt v.v_expr name ^ ";\n"

(* Generates a structure by calling recursively generate_struct_var *)
let rec generate_struct_vars_decl name = function
    | [] -> ""
    | a::q -> generate_struct_var a name ^ generate_struct_vars_decl name q

(* Helper function to generate one variable un a structure without possible initial value *)
let generate_struct_state_var (v : Tast.variable_def) =
    v.v_name ^ ": " ^ generate_type v.v_type ^ ";\n"

(* Calls recursively generate_struct_state_var to generate a whole structure *)
let rec generate_struct_state_vars_decl = function
    | [] -> ""
    | a::q -> generate_struct_state_var a ^ generate_struct_state_vars_decl q

(* The global state of the contract comprises its state variables. We store and pass them as a record in Coq.
This function generates the structure to contain all the state variables specifically *)
let generate_state_vars (vars : Tast.variable_def list) (name : ident) =
    List.iter (fun v -> state_list := (v.v_name)::(!state_list); state_vars := VSet.add v.v_name (!state_vars)) vars; 
    "Record " ^ name ^" := create_"^name^" { \n" ^ (generate_struct_state_vars_decl vars) ^ "}.\n"

(* Called at the beginning of each function generation to extract all the values of the state variables passed as a Record to the function *)
let rec create_base_state_vars (vars : Tast.variable_def list) name =
    match vars with
    | [] -> ""
    | a::q -> ("let " ^ a.v_name ^ " := ("^ a.v_name ^ " " ^name^") in\n") ^ (create_base_state_vars q name)

(* Generate one function parameter, and specifies its Coq type *)
let generate_param (param : Tast.type_name * ident) =
    "(" ^ (snd param) ^ ":" ^ (generate_type (fst param)) ^ ") "
    
(* Generates the list of parameters of a function in its Coq prototype *)
let rec generate_func_params (params : (Tast.type_name * ident) list) =
    match params with
    | [] -> ""
    | a::q -> (generate_param a) ^ (generate_func_params q)

(* Generates all the return parameters of a function given its list of return parameters from the AST *)
let rec generate_return_par = function
    | [] -> ""
    | a::q-> ", "^(snd a) ^ (generate_return_par q)

(* When mappings are chained, we access them in a row, and call them imap0, imap1, …
This funtion generates the name of an intermediate map given its id *)
let get_name_map id = function
    | 0 -> id
    | i -> "imap"^(string_of_int i)

(* Returns the value of the element at the end of a chaining of mappings. i.e. mapping (string -> mapping (int, bool)) returns bool *)
let rec get_final_map_type = function
    | TIdent s -> raise (Error "Mapping of custom classes not supported")
    | TMapping (e, t) -> get_final_map_type t
    | TElem e -> e

(* Returns a default value for a possibly chained mapping *)
let rec base_map_nat t = function
    | 0 -> (match get_final_map_type t with
        | TEInt | TEAddress -> string_of_int(0)
        | TEString -> "\"\""
        | TEBool -> "false")
    | i -> "IntMap.empty ("^(base_map_nat_aux t (i-1))^")"

(* Returns the complete type of a possible chained mapping *)
and base_map_nat_aux t = function
    | 0 -> (match get_final_map_type t with
        | TEInt | TEAddress -> "Z"
        | TEString -> "string"
        | TEBool -> "bool")
    | i -> "IntMap.t ("^(base_map_nat_aux t (i-1))^")"

(* Generates accessors for all the intermediate maps in a chained mapping *)
let rec generate_intermediate_maps name id i length t= function
    | [] -> ""
    | a::q -> "let "^(get_name_map id (i+1))^" := match (IntMap.find "^ (generate_expression a name) ^ " " ^ (get_name_map id i) ^ ") with\n |None => "^(base_map_nat t (length-i-1)) ^"\n | Some a => a end in\n" ^ (generate_intermediate_maps name id (i+1) length t q) (* Needs some typing. Not always base_map_nat *)

(* Generates an access in a possible chained mapping *)
let rec generate_map_access id el e i name= match el with
    | [] -> generate_expression e name
    | a::q -> "IntMap.add " ^ (generate_expression a name) ^ " (" ^ (generate_map_access id q e (i+1) name) ^ ")" ^ (get_name_map id i)

(* Generates a variable assignment *)
let rec generate_var_assign name = function
    | VAIdent (op, id, e) -> "let " ^id ^ " := " ^ (match op with
        | Assign -> generate_expression e name
        | AssignAdd -> id ^ " + " ^ (generate_expression e name)
        | AssignSub -> id ^ " - " ^ (generate_expression e name)
        | AssignMul -> id ^ " * " ^ (generate_expression e name)
        ) ^" in \n"
    | VAField (op, e1, id, e2) -> raise (Error ("VAField not implemented"))
    | VAIdentArray (op, id, el, e, t) -> (match op with
        | Assign -> (generate_intermediate_maps name id 0 (List.length el) t el) ^ "let "^id ^ " := " ^ (generate_map_access id el e 0 name) ^" in\n" 
        | AssignAdd -> (generate_var_assign name (VAIdentArray(Assign, id, el, EBinOp(OpPlus, EArrayVar(id, el), e), t)))
        | AssignSub -> (generate_var_assign name (VAIdentArray(Assign, id, el, EBinOp(OpMinus, EArrayVar(id, el), e), t)))
        | AssignMul -> (generate_var_assign name (VAIdentArray(Assign, id, el, EBinOp(OpMul, EArrayVar(id, el), e), t)))
        )
    | VAFieldArray (op, e1, id, el, e2, t) -> raise (Error ("VAFieldArray not implemented"))

(* Generates the complete parameters returned by a function. It consists of the record of state variables corresponding to the new global state, the new ether balances of all Ethereum users and the return values of the function itself *)
let generate_return_params (ret_params : (Tast.type_name * ident) list) name = 
    match ret_params with
    | [] -> "((create_"^name ^ (print_state_vars (List.tl(List.rev((!state_list)))))^ "), new_ether)"
    | l -> "((create_"^name ^ (print_state_vars (List.tl(List.rev(!state_list)))) ^"), new_ether"^ (generate_return_par l) ^")\n"

(* Generate return values during a throw *)
let rec generate_throw_par = function
    | [] -> ""
    | a::q -> ", "^(snd a) ^ (generate_throw_par q)

(* Generate the complete throw parameters, including the initial global state and initial ether balances *)
let generate_throw_return (ret_params : (Tast.type_name * ident) list) name = 
    match ret_params with
    | [] -> "(" ^ name ^ ", ether)"
    | l -> "("^name ^ ", ether" ^ (generate_throw_par l) ^ ")\n"

(* Helper function used during the declaration of variables. If no initial value was specified, a default one is created *)
let generate_expr_opt_vardecl (eo : Tast.expression option) (t : Tast.type_name) name =
    match eo with
    | None -> (match t with
        | TIdent id -> raise (Error ("Initialization of complex types not supported"))
        | TMapping (e, m) -> init_mapping e m 
        | TElem e -> (match e with
            | TEInt | TEAddress -> "0 "
            | TEBool -> "false "
            | TEString -> add_required "String"; open_string := true; "\"\"")
        )
    | Some e -> generate_expression e name

(* Generates a variable, with the specified value if there is one, with a default value if not *)
let generate_var_decl (v : Tast.variable_def) name =
    "let " ^v.v_name ^ " := " ^ (generate_expr_opt_vardecl v.v_expr v.v_type name) ^" in\n"

(* Returns true if a list of instructions ends with a return, exception or if/then/else block *)
let ends_with_Return l =
    match (List.hd (List.rev l)) with
        | SReturn _  | SThrow | SIfElse _-> true
        | _ -> false

(* Returns true if a statement or a block ends with a return *)
let block_ends_with_return = function
    | SBlock st -> ends_with_Return st
    | SReturn _ | SThrow | SIfElse _ -> true
    | _ -> false

(* Returns true if a list of instructions ends with a return, exception or if/then/else block *)
let list_ends_with_Return = function
    | [] -> false
    | l -> ends_with_Return l

(* A loop is compiled as an auxiliary instruction. To pass the complete scope of variables, we use a Record. This function generates this structure *)
let rec generate_while_struct = function 
    | [] -> ""
    | a::q -> (fst a) ^ (string_of_int (!count_while)) ^ " : " ^ (snd a) ^ ";\n" ^ generate_while_struct q

(* Generates the declaration of the list of variables in scope of a loop *)
let rec generate_while_vars i str = function
    | [] -> ""
    | a::q -> "let " ^ (fst a) ^ " := (" ^ (fst a) ^ (string_of_int i) ^ " "^str^ (string_of_int i) ^ ") in\n" ^ (generate_while_vars i str q)

(* Prints the name of all variables in the scope of a loop *)
let rec print_while_vars = function
    | [] -> ""
    | a::q -> (fst a) ^ " " ^ (print_while_vars q)

(* Generates instructions inside a loop *)
let rec generate_while_statement name = function
    | SIf (e, st, cont) -> raise (Error ("if in while unsupported"))
    | SIfElse (e, st1, st2, cont) -> raise (Error ("ifelse in while unsupported"))
    | SWhile (e, s) -> raise (Error ("imbricated while not supported"))
    | SBlock (sl) -> generate_while_statements name sl 
    | SReturn eo -> raise (Error ("return in while not supported"))
    | SThrow -> raise (Error ("throw in while not supported"))
    | SExpr e -> generate_expression e name 
    | SVarDecl v -> generate_var_decl v name 
    | SVarAssign va -> generate_var_assign name va 

(* Recursively generates the core of a loop *)
and generate_while_statements name = function
    | [] -> ""
    | a::q -> (generate_while_statement name a) ^ (generate_while_statements name q)

(* Completly generates the auxiliary function to model a loop. It updates the while_structs and while_functions references, to be added at the beginning of the Coq code *)
let generate_while_auxfunction e s vars name = 
    while_structs := (!while_structs) ^ "Record whilestruct" ^ (string_of_int (!count_while)) ^ " := create_whilestruct" ^ (string_of_int (!count_while)) ^ " {\n" ^ (generate_while_struct vars) ^ "}.\n"; 
    while_functions := (!while_functions) ^ "Fixpoint whilefunction" ^ (string_of_int (!count_while)) ^ " (msg : Message) gas (input"^(string_of_int (!count_while))^" : whilestruct" ^ (string_of_int (!count_while)) ^ ") := \n" ^ (generate_while_vars (!count_while) "input" vars) ^ "match gas with
    | O => (gas, create_whilestruct"^(string_of_int (!count_while)) ^ " "^ (print_while_vars vars) ^") " ^ 
    "\n | S g => let new_gas := g in\n" ^ 
    "if (" ^ (generate_expression e name) ^ ") then (" ^ (generate_while_statements name s) ^ "whilefunction"^ (string_of_int (!count_while)) ^ " msg new_gas (create_whilestruct"^(string_of_int (!count_while)) ^ " " ^ (print_while_vars vars) ^")) else \n" ^ "(new_gas, create_whilestruct"^(string_of_int (!count_while)) ^ " " ^ (print_while_vars vars) ^") end.\n";
     count_while := (!count_while) + 1;
     "let (new_gas, result"^(string_of_int ((!count_while) -1)) ^ ") := whilefunction" ^ (string_of_int ((!count_while) - 1)) ^ " msg new_gas (create_whilestruct" ^ (string_of_int ((!count_while) - 1)) ^ " " ^ (print_while_vars vars) ^ ") in\n" ^ (generate_while_vars ((!count_while) -1) "result" vars) 

(* Generates a statement. An if or if/else statement has to merge the control flow after it, thus two paths are created by copying the instructions remaining after it.
We also keep the list of variables currently in the context as *vars* to pass it to a loop auxiliary function if we need one *)
let rec generate_statement (s : Tast.statement) ret_params name vars = match s with
    | SIf (e, st, cont) -> "if (" ^ (generate_expression e name) ^ ") then (" ^ (generate_statement st ret_params name vars) ^ (if (block_ends_with_return st) then "" else ((generate_insns cont ret_params name vars) ^ (if list_ends_with_Return cont then  "" else generate_return_params ret_params name))) ^ ") \n else " 
    | SIfElse (e, st1, st2, cont) -> "if (" ^ (generate_expression e name) ^ ") then (" ^ (generate_statement st1 ret_params name vars) ^ (if (block_ends_with_return st1) then "" else ((generate_insns cont ret_params name vars) ^ (if list_ends_with_Return cont then "" else generate_return_params ret_params name))) ^ ") \nelse (" ^ (generate_statement st2 ret_params name vars) ^ (if (block_ends_with_return st2) then "" else ((generate_insns cont ret_params name vars) ^ (if list_ends_with_Return cont then "" else generate_return_params ret_params name))) ^ ")\n"
    | SWhile (e, s) -> generate_while_auxfunction e s vars name
    | SBlock (sl) -> generate_insns sl ret_params name vars
    | SReturn (eo) -> (match eo with 
        | None -> generate_return_params ret_params name
        | Some (EFunCall (id, e)) -> generate_expression (EFunCall (id, e)) name
        | Some e -> "(create_"^name ^ (print_state_vars (List.tl(List.rev((!state_list))))) ^ ", new_ether, "^ (generate_expression e name) ^")\n"
        )
    | SThrow -> generate_throw_return ret_params name 
    | SExpr e -> generate_expression e name
    | SVarDecl v -> generate_var_decl v name 
    | SVarAssign va -> generate_var_assign name va 

(* Generates recursively the list of instructions in a function, by calling generate_statement.
If we declare a new variable, we add it to the current context of variables *vars* to use it for the generation of loops in generate_statement *)
and generate_insns (insns : Tast.statement list) ret_params name vars  = match insns with
    | [] -> ""
    | a::q -> (match a with 
        | SIfElse _ -> (generate_statement a ret_params name vars)
        | SVarDecl v -> (generate_statement a ret_params name vars) ^ (generate_insns q ret_params name (((v.v_name, generate_type v.v_type)::vars)))
        | _ -> (generate_statement a ret_params name vars) ^ (generate_insns q ret_params name vars)
    )

(* Creates an initial default value for an element of type t *)
let initialize_value (t : Tast.type_name) name =
    match t with
    | TIdent id -> raise (Error ("Initialization of complex types not supported in initialize_value"))
    | TMapping (e, m) -> init_mapping e m 
    | TElem e -> (match e with 
            | TEInt | TEAddress -> "0"
            | TEBool -> "false"
            | TEString -> add_required "String"; open_string := true; "\"\""
            )

(* Generates placeholder values for all the return parameters, corresponding to the 0 representation in Solidity.
These values are thus returned directly if the return parameters are never initialized in the Solidity code, as specified in the Solidity semantics *)
let rec create_base_return (ret_params : (Tast.type_name * ident) list) name = 
    match ret_params with
        | [] -> "let new_ether := ether in \n"
        | a::q -> "let " ^ (snd a) ^" := "^ (initialize_value (fst a) (snd a)) ^ " in \n"^ (create_base_return q name)

(* For a contract constructor, values are initialized as written in the Solidity code, and the untouched values are given a 0 representation as an initial value.
This function creates the 0 default representation for all the state variables in the Coq code of the constructor *)
let rec create_constr_state_vars (vars : Tast.variable_def list) name = 
    match vars with
    | [] -> "let new_ether := ether in\n"
    | a::q -> ("let " ^ a.v_name ^ " := "^(initialize_value a.v_type a.v_name) ^ " in\n") ^ (create_constr_state_vars q name)

(* Creates a list of all parameters of a function, with the form (name : type) *)
let rec collect_func_params = function
    | [] -> [] 
    | a::q -> ((snd a, generate_type (fst a)))::(collect_func_params q)

(* Creates a list of all state variables of the contract, with the form (name : type) *)
let rec collect_base_state_vars = function
    | [] -> []
    | a::q -> ((a.v_name, generate_type a.v_type))::(collect_base_state_vars q)

(* Creates a list of all return parameters of a function, with the form (name : type) *)
let rec collect_base_return = function
    | [] -> []
    | a::q -> ((snd a, generate_type (fst a)))::(collect_base_return q) 

(** 
Generation of a function: All functions are declared in Coq as recursive to be able to model a possible reentrancy.
We distinguish between two cases: the function is the contract constructor, in this case we create a new coherent global state, and the function is not.
We currently have a simple model of gas consumption: at each function call, we decrease by one the amount of gas. 
If we don't have gas left, we throw an exception, and return the initial values of the input parameters. This ensures the terminaison in Coq.
We give as input parameters of the function the amount of gas, the global state of the contract containing all state variables, the ether balances of all users,
the message sent by an user to execute a function, and finally the actual input parameters of the function if there are any.
We finally generate all the function statements in Coq, and add to these a return statement if the Solidity code didn't end with a return or a throw.
**)
let generate_function (f : Tast.function_def) name c_vars = 
if not (f.func_insns = []) then (
    "Fixpoint " ^ (if (name = f.func_name) then name^"_constructor" else f.func_name ^ " gas (" ^ name ^ ":" ^ name ^ ") ") ^ ("(ether : EtherMap) (msg : Message)") ^ (generate_func_params f.func_params) ^ " := \n" ^ (if (name = f.func_name) then (create_constr_state_vars c_vars name) else (create_base_state_vars c_vars name) ^ (create_base_return f.func_ret_params name)) ^ (if (name = f.func_name) then "" else "match gas with
    | O => "^ (generate_return_params f.func_ret_params name) ^ 
    "\n | S g => let new_gas := g in\n") ^ (generate_insns f.func_insns f.func_ret_params name (("new_ether", "EtherMap")::(collect_func_params f.func_params)@(collect_base_state_vars c_vars)@(collect_base_return f.func_ret_params))) ^ (if not (ends_with_Return f.func_insns) then (generate_return_params f.func_ret_params name) else "") ^ (if (name = f.func_name) then ".\n" else "end.\n"))
    else ""

(* Generates all the functions in the contract by recursively calling generate_function.
c_vars is here the list of state variables of the contract, that are automatically in the context of any function *)
let rec generate_functions (funs : Tast.function_def list) (name : ident) c_vars =
match funs with 
    | [] -> ""
    | a::q -> (generate_functions q name c_vars) ^ (generate_function a name c_vars)
    
(* Generates structures in the contract. Not implemented yet *)
let generate_struct_vars (sts : Tast.struct_def list) name =
    match sts with
        | [] -> ""
        | a::q -> raise (Error ("struct definition not implemented"))

(* Generates the anonymous "()" function of the contract. This function is called in Solidity when ether is sent to the contract. Its generation is similar to other functions *)
let generate_anonymous_fun (insns : Tast.statement list) name =
    if insns != [] then (
    "Definition anonymous_function ("^ name ^ " : " ^name ^") (ether : EtherMap) (msg : Message) :=\n" ^ (create_base_return [] name) ^ (generate_insns insns [] name [("new_ether", "EtherMap")]) ^ (if not (ends_with_Return insns) then (generate_return_params [] name) else "") ^ ".\n" ) else ""


(* Generates a default value for the last element at the end of a chain of mappings. For instance, 0 for mapping (string -> mapping (bool, int)) *)
let rec create_base_final_value = function
    | TMapping(e, t) -> create_base_final_value t
    | TIdent _ -> raise (Error "map of idents not supported")
    | TElem e -> (match e with 
        | TEInt | TEAddress -> "0"
        | TEBool -> "false"
        | TEString -> "\"\""
        )

(* Helper function to generate accessors for intermediate mappings in a chain of mappings *)
let matching_for_accessor i = function
    | TIdent _ -> raise (Error "Ident maps not supported")
    | TMapping (e, t) -> "| None => None \n | Some a => IntMap.find a"^(string_of_int i)^ " a"
    | TElem t -> "| None => " ^(create_base_final_value (TElem t)) ^ "\n | Some a => a"

(* Creates of an accessor for the i-th intermediate mapping *)
let rec create_match_accessor i curr_str= function
    | TMapping (el, t) -> "let m"^(string_of_int (i+1)) ^  ":= match "^(if (curr_str = "mapping") then  ("(IntMap.find a"^(string_of_int i) ^ " " ^ curr_str ^ ") ") else ("m"^(string_of_int i)))^ " with\n " ^ (matching_for_accessor i t) ^ " end in \n" ^ (create_match_accessor (i+1) ("m"^(string_of_int (i+1))) t)
    | t -> "m"^(string_of_int i) 

(* Generates input parameters for creating an accessor of the whole mapping *)
let rec generate_n_ints i= function
    | TMapping (el, t) -> "(a" ^ (string_of_int i) ^ " : Z) " ^ (generate_n_ints (i+1) t) 
    | _ -> ""

(* Maps in Coq and Solidity have a slightly different behaviour. In Solidity, if the key is not in the map, a "0" value is returned when accessing it.
In Coq, accessing a key k returns Some a if there was something previously stored, None if not.
We thus generate accessors for all state variables maps in the contract *)
let rec create_accessors = function
    | [] -> ""
    | a::q -> (match a.v_type with
        | TMapping _ -> "Definition get_"^a.v_name ^" (mapping : " ^ (generate_type a.v_type) ^" ) " ^ (generate_n_ints 0 a.v_type) ^ ":= \n" ^ (create_match_accessor 0 "mapping" a.v_type) ^ ".\n" ^ (create_accessors q)
        | _ -> "")

(** 
The following functions are used to generate Coq theorems for properties written in annotations in Solidity.
They also generate the helper lemmas corresponding to the property we are trying to prove.
Currently, we only target preservation properties, i.e. proving that a state variable or
an expression involving a state variable remains constant throughout any execution of the contract.
We thus express that this quantity is preserved though the execution of any public function with any parameters
 **)

(* Retrieves the type of the variable specified in the annotation from the list of state variables *)
let rec get_annot_var_type var = function
    | [] -> raise (Error (var ^ " is not a state variable valid for the annotation"))
    | a::q -> (if (a.v_name = var) then a.v_type else get_annot_var_type var q)

(* Returns the list of parameters required in a lemma *)
let rec lemma_func_params = function
    | [] -> ""
    | a::q -> " " ^ (snd a) ^ lemma_func_params q

(** 
Generates the list of Lemmas to prove the preservation of a property, when the variable v involved in the property has a simple type (i.e. not a mapping or an object)
For each function f in the contract, we generate a lemma preservation_f_v that expresses that the expression with v is invariant through any execution of f.
We finally use Admitted as placeholder to have a correct Coq code, and let the proof of the lemma to the user.
**)
let rec generate_simple_annot (annot : Tast.annotation_def) name = function
    | [] -> ""
    | a::q -> if (List.mem a.func_name annot.an_funs || (name = a.func_name)) then "" else "Lemma preservation_"^(a.func_name)^"_"^(annot.an_var)^" : forall (" ^ name ^ " : " ^ name ^ ") " ^ (generate_func_params a.func_params) ^ ", \n let " ^ name ^ "_2 := "^ 
    (match a.func_ret_params with
        | h::l -> " fst( " ^ (a.func_name) ^ " " ^ name ^  (lemma_func_params a.func_params) ^ ")" 
        | [] -> (a.func_name) ^ " " ^ name ^  (lemma_func_params a.func_params) ) 
    ^ " in\n (" ^ (annot.an_var) ^ " " ^ name ^ ") = (" ^ (annot.an_var) ^" " ^ name ^"_2)" ^ 
    ".\nAdmitted.\n\n " ^ (generate_simple_annot annot name q)

(** 
Generates the list of Lemmas to prove the preservation of a property, when the variable v involved in the property has a mapping type
For each function f in the contract, we generate a lemma preservation_f_v that expresses that the expression with v is invariant through any execution of f.
The lemma generated expresses that the sum of eval(x) on all elements of the mapping, where eval is the function specified in the annotation, is preserved.
We finally use Admitted as placeholder to have a correct Coq code, and let the proof of the lemma to the user.
**)
let rec generate_mapping_annot (annot : Tast.annotation_def) name = function
    | [] -> ""
    | a::q -> if (List.mem a.func_name annot.an_funs || (name = a.func_name)) then "" else "Theorem preservation_"^(a.func_name)^"_"^(annot.an_var)^" : forall (" ^ name ^ " : " ^ name ^") (ether : EtherMap) (msg : Message)" ^ (generate_func_params a.func_params) ^ ", \n let " ^ name ^ "_2 := " ^
    ( " fst( " ^(a.func_name) ^ " " ^ name ^" ether msg" ^(lemma_func_params a.func_params) ^ ")")
    ^" in\n (sum_" ^ (annot.an_var) ^ " (IntMap.elements ("^(annot.an_var) ^ " "  ^ name ^ "))) = ( sum_" ^ (annot.an_var) ^ " (IntMap.elements (" ^ (annot.an_var) ^ " " ^ name ^"_2)))" ^
    ".\nAdmitted.\n\n" ^ (generate_mapping_annot annot name q)

(* Generates the evaluation function for the annotation involving a mapping m, and adds the required Coq modules *)
let generate_mapping_annot_function name annot m exp =
    add_required "List"; "Definition mapping_function_"^(annot.an_var) ^ " ( x : Z * " ^ (generate_type m) ^ ") := \n " ^ (generate_expression exp name) ^ ".\n" ^ 
    "Fixpoint sum_"^(annot.an_var)^" (maplist : list (Z * "^(generate_type m) ^")) := \n match maplist with
    | nil => 0
    | a::q => (mapping_function_"^(annot.an_var) ^ " a) + (sum_"^(annot.an_var) ^ " q)\nend.\n"

(** 
Generates all the functions required to express a property specified as an annotation.
If the variable v specified in the annotation is a mapping, we first generate the evaluation function specified by calling generate_mapping_annot_function, 
and then generate all the lemmas needed with generate_mapping_annot.
If not, we simply generate all the lemmas required by using generate_simple_annot
**)
let generate_annot (annot : Tast.annotation_def) name (funs : Tast.function_def list) (state_vars : Tast.variable_def list)  = 
    match get_annot_var_type annot.an_var state_vars with
    | TIdent d -> raise (Error ("Custom classes not supported for variables in annotations"))
    | TMapping (e, m) -> (match annot.an_count_elem with
        | None -> raise (Error ("Mapping without a count functions for its elements")) 
        | Some exp -> add_required "Coq.Program.Equality"; add_required "OrderedType"; (generate_mapping_annot_function name annot m exp) ^ (Lemmas.generate_intermediate_lemmas annot.an_var name (generate_type m)) ^ (generate_mapping_annot annot name funs ))
    | TElem e -> generate_simple_annot annot name funs 

(* Generates all the lemmas corresponding to the annotations by calling generate_annot for all annotations in the contract *)
let rec generate_annotations (annots : Tast.annotation_def list) name (funs : Tast.function_def list) (svars : Tast.variable_def list) = match annots with
    | [] -> ""
    | a::q -> (generate_annot a name funs svars) ^ (generate_annotations q name funs svars) 

(* Generates several helper lemmas to speed up the proof *)
let generate_lemmas name = Lemmas.generate_helper_lemmas ()

(**
End of the generation of annotations
**)

(* Models the send function as well as the ether balances *)
let create_ethermap_and_send () = 
    "Definition EtherMap := IntMap.t Z.

Definition get_ether (addr : Z) map : Z :=
    match (IntMap.find addr map) with
    | None => 0
    | Some a => a
    end.

Definition send addr value map :=
    if (Z.leb value (get_ether contract_addr map)) then
        (let map_bis := IntMap.add contract_addr ((get_ether contract_addr map) - value) map in
        let map_bis := IntMap.add addr ((get_ether addr map_bis) + value) map_bis in
        (true, map_bis))
    else (false, map).
\n"

(* Structure for the message sent by the user to the Ethereum Virtual Machine *)
let create_message () = 
    "Record Message := create_message {
sender : Z;
value : Z;
}.\n"

(**
This function generates the whole contract in Coq.
It calls all the functions previously defined.
It first generates the state variables, and store them in the references state_vars and state_list
It then generates the whole contract, by concatening thei definition for the ether balances, send function, messages,
generated auxiliary loop functions, functions, and finally lemmas for annotations.
**)
let codegen_file (contract : Tast.contract_def) = 
    List.iter (fun x -> fun_names := (x.func_name)::(!fun_names)) contract.c_funs;
    let state_decl = generate_state_vars (contract.c_vars) (contract.c_name) in
    let gen_func = generate_functions (contract.c_funs) (contract.c_name) (contract.c_vars) in
    let an_func = generate_anonymous_fun (contract.c_anonymousfun) (contract.c_name) in
    let annot_func = generate_annotations (contract.c_annotations) (contract.c_name) (contract.c_funs) (contract.c_vars) in
   ("Definition contract_addr := 0.\n") ^ (create_ethermap_and_send ()) ^ (create_message ()) ^ state_decl ^ (create_accessors (contract.c_vars)) ^ (!while_structs) ^ (!while_functions) ^(generate_struct_vars (contract.c_structs) (contract.c_name)) ^ gen_func ^ an_func ^ (generate_lemmas contract.c_name) ^ (Lemmas.generate_extract_sorted_lemma ())^ annot_func
   
(* Imports the Coq module that were marked as required *)
let rec create_required_modules = function
        | [] -> ""
        | a::q -> "Require Import " ^ a ^".\n" ^ (create_required_modules q)

(* The entry point of this module. It imports all the required Coq modules by calling create_required_modules, add useful headers
and finally generates the contract by calling codegen_file *)
let codegen (file : Tast.file) = 
    (create_required_modules (!required_modules)) ^ 
    (if (!open_string) then "Open Scope string_scope.\n" else "") ^
    ("Open Scope Z_scope.\nInclude BinIntDef.Z.\n") ^
    ("Module IntMap := FMapList.Make(Z_as_OT).\n") ^
    (codegen_file (List.hd file.f_contracts))
