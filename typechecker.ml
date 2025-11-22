open Ast
open Astlib
open Tctxt

(* Error Reporting ---------------------------------------------------------- *)
(* NOTE: Use type_error to report error messages for ill-typed programs. *)

exception TypeError of string

let type_error (l : 'a node) err =
  let (_, (s, e), _) = l.loc in
  raise (TypeError (Printf.sprintf "[%d, %d] %s" s e err))

let all_true (l : bool list) : bool = List.for_all (fun x -> x) l

let has_duplicates lst =
  let rec aux = function
    | [] -> false
    | x :: xs -> List.mem x xs || aux xs
  in
  aux lst

let flip (p:'a * 'b) = let (x,y) = p in (y,x)


(* initial context: G0 ------------------------------------------------------ *)
(* The Oat types of the Oat built-in functions *)
let builtins =
  [ "array_of_string",  ([TRef RString],  RetVal (TRef(RArray TInt)))
  ; "string_of_array",  ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", ([TRef RString],  RetVal TInt)
  ; "string_of_int",    ([TInt], RetVal (TRef RString))
  ; "string_cat",       ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     ([TRef RString],  RetVoid)
  ; "print_int",        ([TInt], RetVoid)
  ; "print_bool",       ([TBool], RetVoid)
  ]

(* binary operation types --------------------------------------------------- *)
let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)
  | Eq | Neq -> failwith "typ_of_binop called on polymorphic == or !="

(* unary operation types ---------------------------------------------------- *)
let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* subtyping ---------------------------------------------------------------- *)
(* Decides whether H |- t1 <: t2
    - assumes that H contains the declarations of all the possible struct types

    - you will want to introduce addition (possibly mutually recursive)
      helper functions to implement the different judgments of the subtyping
      relation. We have included a template for subtype_ref to get you started.
      (Don't forget about OCaml's 'and' keyword.)
*)
let rec subtype (c : Tctxt.t) (t1 : Ast.ty) (t2 : Ast.ty) : bool =
  if t1=t2 then true else
    match t1,t2 with
    | TNullRef rt1, TNullRef rt2 -> subtype_ref c rt1 rt2
    | TRef rt1, TRef rt2 -> subtype_ref c rt1 rt2
    | TRef rt1, TNullRef rt2 -> subtype_ref c rt1 rt2
    | _ -> false

(* Decides whether H |-r ref1 <: ref2 *)
and subtype_ref (c : Tctxt.t) (t1 : Ast.rty) (t2 : Ast.rty) : bool = match t1,t2 with
  | RString, RString -> true
  | RArray arr_t1, RArray arr_t2 -> arr_t1=arr_t2
  | RStruct s1, RStruct s2 ->
    let s1_struct_ty= lookup_struct_option s1 c
    and s2_struct_ty= lookup_struct_option s2 c in
    let rec isPrefix l1 l2 =
      match l1,l2 with
      | [], _ -> true
      | _, [] -> false
      | h1::t1, h2::t2 -> if h1=h2 then isPrefix t1 t2 else false in
    begin match s1_struct_ty,s2_struct_ty with
      |None, _ | _, None -> false
      | Some field_list_s1, Some field_list_s2 ->
        isPrefix field_list_s2 field_list_s1
        (*not @@ List.mem false @@ List.map (fun x -> List.mem x field_list_s1) field_list_s2*)
    end
  | (RFun (args_t1,rty_t1)),(RFun (args_t2, rty_t2)) ->
    List.length args_t1 = List.length args_t2 &&
    not @@ List.mem false @@ List.map2 (subtype c) args_t2 args_t1 &&
    subtype_retty c rty_t1 rty_t2


  | _ -> false

(*decides wherether H |- rt1 <: rt2 *)
and subtype_retty (c : Tctxt.t) (rt1 : Ast.ret_ty) (rt2 : Ast.ret_ty) : bool = match rt1,rt2 with
  | RetVoid, RetVoid -> true
  | RetVal t1, RetVal t2 -> subtype c t1 t2
  | _ -> false


(* well-formed types -------------------------------------------------------- *)
(* Implement a (set of) functions that check that types are well formed according
   to the H |- t and related inference rules

    - the function should succeed by returning () if the type is well-formed
      according to the rules

    - the function should fail using the "type_error" helper function if the
      type is not well-formed

    - l is just an ast node that provides source location information for
      generating error messages (it's only needed for the type_error generation)

    - tc contains the structure definition context
 *)
let rec typecheck_ty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ty) : unit = match t with
  | TInt | TBool-> ()
  | TRef r | TNullRef r -> typecheck_refty l tc r

and typecheck_refty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.rty) : unit = match t with
  | RString -> ()
  | RArray t_arr ->typecheck_ty l tc t_arr
  | RStruct struct_id -> let struct_ty = lookup_struct_option struct_id tc in
    begin match struct_ty with
    | None -> type_error l ("Undefined struct type: " ^ struct_id)
    | Some _ -> ()
    end
| RFun (args, ret_ty) -> typecheck_returnty l tc ret_ty ; List.iter (typecheck_ty l tc) args
and typecheck_returnty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ret_ty) : unit = match t with
  | RetVoid -> ()
  | RetVal ty -> typecheck_ty l tc ty

(* typechecking expressions ------------------------------------------------- *)
(* Typechecks an expression in the typing context c, returns the type of the
   expression.  This function should implement the inference rules given in the
   oad.pdf specification.  There, they are written:

       H; G; L |- exp : t

   See tctxt.ml for the implementation of the context c, which represents the
   four typing contexts: H - for structure definitions G - for global
   identifiers L - for local identifiers

   Returns the (most precise) type for the expression, if it is type correct
   according to the inference rules.

   Uses the type_error function to indicate a (useful!) error message if the
   expression is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   Notes: - Structure values permit the programmer to write the fields in any
   order (compared with the structure definition).  This means that, given the
   declaration struct T { a:int; b:int; c:int } The expression new T {b=3; c=4;
   a=1} is well typed.  (You should sort the fields to compare them.)

*)
let rec typecheck_exp (c : Tctxt.t) (e : Ast.exp node) : Ast.ty = match e.elt with
  | CNull ref_ty -> TNullRef ref_ty
  | CBool _ -> TBool
  | CInt _ -> TInt
  | CStr _ -> TRef RString
  | Id name when List.mem name (List.map fst c.locals) -> lookup_local name c
  | Id name -> (try lookup_global name c with Not_found -> type_error e ("no type is known for identifier " ^ name))
  | CArr (arr_ty,init_list) ->
    let all_initializers_match_type =all_true @@ List.map (fun x -> subtype c (typecheck_exp c x) arr_ty) init_list in
    if typecheck_ty e c arr_ty;all_initializers_match_type then TRef (RArray arr_ty) else type_error e ("Mismatch in initalizers for array")
  | NewArr (arr_ty,size_node,x, exp_2) ->
    typecheck_ty e c arr_ty;
    if typecheck_exp c size_node <> TInt then type_error e "Array size must be an integer";
    if lookup_local_option x c <> None then type_error e ("Identifier " ^ x ^ " already bound in local context");
    let expanded_context = add_local c x TInt in
    let exp2_type = typecheck_exp expanded_context exp_2 in
    if not (subtype c exp2_type arr_ty) then type_error e "Array initializer type mismatch";
    TRef (RArray arr_ty)
  | Index (array, index) ->
  let type_of_array = match typecheck_exp c array with
    | TRef (RArray t) -> t
    | TNullRef (RArray t) -> type_error e ("Cannot index into nullable array reference")
    | _ -> type_error e ("Indexing non-array type") in
  let index_is_int = (typecheck_exp c index = TInt) in
  if index_is_int then type_of_array else type_error e ("Index is not an integer")
  | Length arr ->
    begin match typecheck_exp c arr with
    | TRef (RArray _) -> TInt
    | TNullRef (RArray _) -> type_error e ("Cannot get length of nullable array reference")
    | _ -> type_error e ("Length applied to non-array type")
    end
  | CStruct (struct_typename ,assignment_list) ->
  let expected_struct_fields = match lookup_struct_option struct_typename c with
    | None -> type_error e ("Undefined struct type: " ^ struct_typename)
    | Some fields -> List.map (fun f -> (f.fieldName, f.ftyp)) fields in
  let assigned_names = List.map fst assignment_list in
  if has_duplicates assigned_names then type_error e "Duplicate fields in struct initialization";
  let sorted_expected_struct_fields = List.sort (fun (name1, _) (name2, _) -> String.compare name1 name2) expected_struct_fields in
  let struct_fields = List.map (fun (name, exp) -> (name, typecheck_exp c exp)) assignment_list in
  let sorted_struct_fields = List.sort (fun (name1, _) (name2, _) -> String.compare name1 name2) struct_fields in
  if List.length sorted_struct_fields <> List.length sorted_expected_struct_fields then
     type_error e "Struct field count mismatch";
  let check_field (actual_name, actual_ty) (expected_name, expected_ty) =
     if actual_name <> expected_name then type_error e ("Field mismatch: expected " ^ expected_name ^ ", got " ^ actual_name);
     subtype c actual_ty expected_ty
  in
  let is_subtype_list = List.map2 check_field sorted_struct_fields sorted_expected_struct_fields in
  if all_true is_subtype_list then TRef (RStruct struct_typename) else type_error e ("Struct field types do not match")
  | Proj (struct_exp, field_name) ->
  let struct_type = match typecheck_exp c struct_exp with
    | TRef (RStruct s) -> s
    | TNullRef (RStruct s) -> type_error e ("Cannot project field from nullable struct reference")
    | _ -> type_error e ("Projection from non-struct type") in
  begin match lookup_field_option struct_type field_name c with
    | None -> type_error e ("Field " ^ field_name ^ " not found in struct " ^ struct_type)
    | Some t -> t
  end
  | Call (fn_exp, arg_exps) ->
    let fn_type = typecheck_exp c fn_exp in
    let arg_types = List.map (typecheck_exp c) arg_exps in
    begin match fn_type with
    | TRef (RFun (param_types, ret_ty)) | TNullRef (RFun (param_types, ret_ty)) ->
      if List.length arg_types <> List.length param_types then
        type_error e "Argument count mismatch";
      begin match ret_ty with
      | RetVoid -> type_error e ("Function has void return type, cannot be used in expression")
      | RetVal ret_type ->
        if all_true @@ List.map2 (subtype c) arg_types param_types
        then ret_type
        else type_error e ("Argument types do not match for function call")
      end
    | _ -> type_error e ("Function call on non-function type")
    end
  | Bop (Eq, a, b) | Bop (Neq, a,b) ->
    let a_type,b_type = typecheck_exp c a, typecheck_exp c b in
    if subtype c a_type b_type && subtype c b_type a_type then TBool else type_error e ("Equality operator type mismatch")
  | Bop (op, a, b) ->
    let (x,y,z) = typ_of_binop op in
    let a_type,b_type = typecheck_exp c a, typecheck_exp c b in
    if a_type= x && b_type = y then z else type_error e ("Binary operator type mismatch")
  | Uop (op, a) ->
    let (x,y) = typ_of_unop op in
    let a_type = typecheck_exp c a in
    if a_type = x then y else type_error e ("Unary operator type mismatch")
  | _ -> failwith "todo: implement remaining expression cases"

(* statements --------------------------------------------------------------- *)

(* Typecheck a statement
   This function should implement the statement typechecking rules from oat.pdf.

   Inputs:
    - tc: the type context
    - s: the statement node
    - to_ret: the desired return type (from the function declaration)

   Returns:
     - the new type context (which includes newly declared variables in scope
       after this statement
     - A boolean indicating the return behavior of a statement:
        false:  might not return
        true: definitely returns

        in the branching statements, both branches must definitely return

        Intuitively: if one of the two branches of a conditional does not
        contain a return statement, then the entier conditional statement might
        not return.

        looping constructs never definitely return

   Uses the type_error function to indicate a (useful!) error message if the
   statement is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   - You will probably find it convenient to add a helper function that implements the
     block typecheck rules.
*)


(* Helper function to check if a block returns without throwing an error *)
let rec block_returns (tc : Tctxt.t) (b : Ast.block) (to_ret : Ast.ret_ty) : bool =
  let fold_function (acc: Tctxt.t * bool) (n:stmt node) =
    let new_ctxt,returns = typecheck_stmt (fst acc) n to_ret in
    if (snd acc) && returns then type_error n "Unreachable statement after definite return";
    (new_ctxt, (snd acc) || returns) in
  snd @@ List.fold_left fold_function (tc, false) b

and typecheck_block (tc : Tctxt.t) (b : Ast.block) (to_ret : Ast.ret_ty) : unit =
  if block_returns tc b to_ret then ()
  else type_error (List.hd b) "Function body does not definitely return"
and  typecheck_stmt (tc : Tctxt.t) (s:Ast.stmt node) (to_ret:ret_ty) : Tctxt.t * bool = match s.elt with
  | Decl (id ,exp_node) -> let exp_ty = typecheck_exp tc exp_node in
    begin match lookup_local_option id tc with
      | Some _ -> type_error s ("Identifier " ^ id ^ " already bound in local context")
      | None -> (add_local tc id exp_ty, false)
    end
  | Assn (lhs, rhs) ->
    begin
      let t,t' = typecheck_exp tc lhs, typecheck_exp tc rhs in
      let t_is_not_global_fun_id = match lhs.elt with
        | Id name -> (try
            let g_ty = lookup_global name tc in
            match g_ty with
            | TRef (RFun _) -> false
            | TNullRef (RFun _) -> false
            | _ -> true
          with Not_found -> true)
        | _ -> true in
      let is_subtype = subtype tc t' t in
      let condition= List.mem t (List.map snd tc.locals) || t_is_not_global_fun_id in
      if condition && is_subtype then (tc, false)
      else type_error s ("Assignment type mismatch or assignment to global function identifier")
    end
  | SCall (fn, args) ->
    begin
      let fn_type = typecheck_exp tc fn in
      let arg_types = List.map (typecheck_exp tc) args in
      begin match fn_type with
        | TRef (RFun (param_types, ret_ty)) | TNullRef (RFun (param_types, ret_ty)) ->
          if ret_ty <> RetVoid then
            type_error s ("Function with non-void return type used in statement call") else ();
          if List.length arg_types <> List.length param_types then
            type_error s "Argument count mismatch in statement call" else ();
          if all_true @@ List.map2 (subtype tc) arg_types param_types then
            (tc, false)
          else
            type_error s "Argument types do not match for statement call"
        | _ -> type_error s "Function call on non-function type in statement call"
      end
    end
  | If (cond, yes, no) ->
    begin
      if typecheck_exp tc cond <> TBool then
        type_error s "Condition expression not boolean in if statement";
      let yes_returns = block_returns tc yes to_ret in
      let no_returns = block_returns tc no to_ret in
      let both_return = yes_returns && no_returns in
      (tc, both_return)
    end
  | Cast (ref,x,expr, yes, no) ->
    begin
      let exp_ty = typecheck_exp tc expr in
      begin match exp_ty with
        | TNullRef ref' ->
          if not @@ subtype_ref tc ref' ref then
            type_error s "Cast type mismatch";
          let expanded_context = add_local tc x (TRef ref) in
          let yes_returns = block_returns expanded_context yes to_ret in
          let no_returns = block_returns tc no to_ret in
          let both_return = yes_returns && no_returns in
          (tc, both_return)
        | _ -> type_error s "Cast expression must be a possbly-null reference type"
      end
    end
  | While (cond, block) ->
    if typecheck_exp tc cond <> TBool then
      type_error s "Condition expression not boolean in while statement"
    else
      ignore (block_returns tc block to_ret);
      (tc, false)
  |For (vdecls,Some cond,Some stmt, block) ->
  let vdecls_stmts = List.map (fun vd -> {elt=Decl vd; loc=s.loc}) vdecls in
  let fold_function = fun (context:Tctxt.t) (n:stmt node) ->
    let new_ctxt,_ = typecheck_stmt context n to_ret in
    new_ctxt in
  let expanded_context = List.fold_left fold_function tc vdecls_stmts in
  if typecheck_exp expanded_context cond <> TBool then
    type_error s "Condition expression not boolean in for statement"
  else
    (match stmt.elt with
    | Assn _ | SCall _ -> ()
    | _ -> type_error s "For loop update must be assignment or function call");
    let _,_ = typecheck_stmt expanded_context stmt to_ret in
    ignore (block_returns expanded_context block to_ret);
    (tc, false)
  | Ret None -> 
    if to_ret <> RetVoid then type_error s "Return type mismatch: expected non-void return";
    (tc,true)
  | Ret (Some expr) ->
  let return_ty= match to_ret with
    | RetVoid -> type_error s "Return type mismatch: expected void"
    | RetVal t -> t in
  let exp_ty = typecheck_exp tc expr in
  if subtype tc exp_ty return_ty then (tc,true) else type_error s "Return type mismatch"
  | _ -> failwith "todo: implement remaining statement cases"



(* struct type declarations ------------------------------------------------- *)
(* Here is an example of how to implement the TYP_TDECLOK rule, which is
   is needed elswhere in the type system.
 *)

(* Helper function to look for duplicate field names *)
let rec check_dups fs =
  match fs with
  | [] -> false
  | h :: t -> (List.exists (fun x -> x.fieldName = h.fieldName) t) || check_dups t

let typecheck_tdecl (tc : Tctxt.t) id fs  (l : 'a Ast.node) : unit =
  if check_dups fs
  then type_error l ("Repeated fields in " ^ id)
  else List.iter (fun f -> typecheck_ty l tc f.ftyp) fs

(* function declarations ---------------------------------------------------- *)
(* typecheck a function declaration
    - extends the local context with the types of the formal parameters to the
      function
    - typechecks the body of the function (passing in the expected return type
    - checks that the function actually returns
*)
let typecheck_fdecl (tc : Tctxt.t) (f : Ast.fdecl) (l : 'a Ast.node) : unit =
  (* Validate parameter types are well-formed *)
  List.iter (fun (param_ty, _) -> typecheck_ty l tc param_ty) f.args;
  (* Validate return type is well-formed *)
  typecheck_returnty l tc f.frtyp;
  (* Check for duplicate parameter names *)
  if has_duplicates @@ List.map snd f.args then
    raise (TypeError ("Duplicate parameter names in function " ^ f.fname));
  (* Typecheck the function body *)
  let expanded_context = add_locals tc (List.map flip f.args) in
  typecheck_block expanded_context f.body f.frtyp

(* creating the typchecking context ----------------------------------------- *)

(* The following functions correspond to the
   judgments that create the global typechecking context.

   create_struct_ctxt: - adds all the struct types to the struct 'H'
   context (checking to see that there are no duplicate fields

     H |-s prog ==> H'


   create_function_ctxt: - adds the the function identifiers and their
   types to the 'G' context (ensuring that there are no redeclared
   function identifiers)

     H ; G1 |-f prog ==> G2


   create_global_ctxt: - typechecks the global initializers and adds
   their identifiers to the 'G' global context

     H ; G1 |-g prog ==> G2


   NOTE: global initializers may mention function identifiers as
   constants, but can't mention other global values *)

let create_struct_ctxt (p:Ast.prog) : Tctxt.t =
  let unwrap x = match x with
    | Gtdecl n -> n.elt
    | _ -> failwith "unwrap: not a type declaration" in
  let is_type_decl p =
    match p with
    | Gtdecl _ -> true
    | _ -> false in
  let decls = List.map unwrap @@ List.filter is_type_decl p in
  if has_duplicates (List.map fst decls) then raise (TypeError "Duplicate struct names");
  let builtin_globals = List.map (fun (name, (args, ret)) ->
    (name, TRef (RFun (args, ret)))) builtins in
  {
    locals = [];
    globals = builtin_globals;
    structs = decls;
  }
let create_function_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  let unwrap x = match x with
    | Gfdecl n -> n.elt
    | _ -> failwith "unwrap: not a function declaration" in
  let is_function_decl p =
    match p with
    | Gfdecl _ -> true
    | _ -> false in
  let decls = List.map unwrap @@ List.filter is_function_decl p in
  let func_names = List.map (fun f -> f.fname) decls in
  if has_duplicates func_names then raise (TypeError "Duplicate function definitions");
  List.iter (fun name -> if List.mem_assoc name tc.globals then raise (TypeError ("Function " ^ name ^ " redefines global"))) func_names;
  let typ_of_fdecl (f:fdecl) : (id*ty)=
    let arg_types = List.map fst f.args in
    (f.fname,TRef (RFun (arg_types,f.frtyp))) in
  add_globals tc (List.map typ_of_fdecl decls)
let create_global_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  let is_vdecl p =
    match p with
    | Gvdecl _ -> true
    | _ -> false in
 let vdecls = List.map (fun x -> match x with
    | Gvdecl n -> n.elt
    | _ -> failwith "unwrap: not a global variable declaration") @@ List.filter is_vdecl p in
 let vdecl_names = List.map (fun x -> x.name) vdecls in
 if has_duplicates vdecl_names then raise (TypeError "Duplicate global variable definitions");
 List.iter (fun name -> if List.mem_assoc name tc.globals then raise (TypeError ("Global " ^ name ^ " redefines existing global"))) vdecl_names;
 let fold_function acc (x:gdecl)=
   try add_global acc x.name (typecheck_exp tc x.init) with _ ->
     type_error x.init ("Error in global variable initializer for " ^ x.name) in
  List.fold_left fold_function tc vdecls


(* This function implements the |- prog and the H ; G |- prog
   rules of the oat.pdf specification.
*)
let typecheck_program (p:Ast.prog) : unit =
  let sc = create_struct_ctxt p in
  let fc = create_function_ctxt sc p in
  let tc = create_global_ctxt fc p in
  List.iter (fun p ->
    match p with
    | Gfdecl ({elt=f} as l) -> typecheck_fdecl tc f l
    | Gtdecl ({elt=(id, fs)} as l) -> typecheck_tdecl tc id fs l
    | _ -> ()) p
