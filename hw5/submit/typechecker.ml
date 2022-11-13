open Ast
open Astlib
open Tctxt

(* Error Reporting ---------------------------------------------------------- *)
(* NOTE: Use type_error to report error messages for ill-typed programs. *)

exception TypeError of string

let type_error (l : 'a node) err = 
  let (_, (s, e), _) = l.loc in
  raise (TypeError (Printf.sprintf "[%d, %d] %s" s e err))


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
let rec is_sublist (l1: 'a list) (l2: 'a list) : bool =
  begin match l1, l2 with
    | [], [] -> true
    | _, [] -> false
    | [], _ -> true
    | (x::xs), (y::ys) -> if (x=y) then is_sublist xs ys else false
end

let rec subtype (c : Tctxt.t) (t1 : Ast.ty) (t2 : Ast.ty) : bool =
  begin match t1, t2 with
    | TInt, TInt -> true
    | TBool, TBool -> true
    | TNullRef nr1, TNullRef nr2 -> subtype_ref c nr1 nr2
    | TRef r1, TRef r2 -> subtype_ref c r1 r2
    | TRef r1, TNullRef nr2 -> subtype_ref c r1 nr2
    | _ , _-> false
end

(* Decides whether H |-r ref1 <: ref2 *)
and subtype_ref (c : Tctxt.t) (t1 : Ast.rty) (t2 : Ast.rty) : bool =
  begin match t1, t2 with
    | RString, RString -> true
    | RArray ty1, RArray ty2 -> (subtype c ty1 ty2) && (subtype c ty2 ty1)
    | RStruct id1, RStruct id2 ->
      if (not ((List.mem_assoc id1 c.structs) && (List.mem_assoc id2 c.structs))) then false
      else 
        let s1 = List.assoc id1 c.structs in
        let s2 = List.assoc id2 c.structs in
        if (is_sublist s2 s1) then true else false
    | RFun (args1,rt1), RFun (args2,rt2) ->
      if (List.length args1 <> List.length args2) then false
      else 
        let mapped_list = List.map2 (subtype c) args2 args1 in
        let folded_list = List.fold_left ( && ) true mapped_list in
        (folded_list && (subtype_rt c rt1 rt2))
    | _ -> false
end
  
and subtype_rt (c : Tctxt.t) (t1 : Ast.ret_ty) (t2 : Ast.ret_ty) : bool =
  begin match t1, t2 with
    | RetVoid, RetVoid -> true
    | RetVal rt1, RetVal rt2 -> subtype c rt1 rt2
    | _ -> false
end

(* well-formed types -------------------------------------------------------- *)
(* Implement a (set of) functions that check that types are well formed according
   to the H |- t and related inference rules

    - the function should succeed by returning () if the type is well-formed
      according to the rules

    - the function should fail using the "type_error" helper function if the 
      type is 

    - l is just an ast node that provides source location information for
      generating error messages (it's only needed for the type_error generation)

    - tc contains the structure definition context
 *)
let rec typecheck_ty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ty) : unit =
  begin match t with
    | TInt -> ()
    | TBool -> ()
    | TRef r -> typecheck_ref l tc r
    | TNullRef nr -> typecheck_ref l tc nr
end

and typecheck_ref (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.rty) : unit =
  begin match t with
    | RString -> ()
    | RArray ty -> typecheck_ty l tc ty
    | RStruct id -> if (List.mem_assoc id tc.structs) then () else type_error l "invalid struct"
    | RFun (args, rt) -> 
      let _ = List.map (typecheck_ty l tc) args in
      typecheck_rt l tc rt     
end

and typecheck_rt (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ret_ty) : unit =
  begin match t with
    | RetVoid -> ()
    | RetVal rt -> typecheck_ty l tc rt
end

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

let rec check_dups_cstruct fields =
  match fields with
  | [] -> false
  | h::t -> (List.exists (fun x -> (fst x) = (fst h)) t) || check_dups_cstruct t

let weird_function x y = x

let typecheck_fty_aux (tc: Tctxt.t) (t: Ast.ty) : bool =
  ((typecheck_ty (no_loc t) tc t) = ()) 

let typecheck_fty (tc: Tctxt.t) (f: Ast.fdecl) : Ast.ty =
  let rt = f.frtyp in
  let args_ty = List.map (fst) f.args in
  let check_rt = ((typecheck_rt (no_loc f) tc rt) = ()) in
  let map_args = List.map (typecheck_fty_aux tc) args_ty in
  let fold_args = List.fold_left ( && ) true map_args in
  if (check_rt && fold_args) then (TRef (RFun (args_ty, rt))) else type_error (no_loc f) "invalid function types"

let rec typecheck_exp (c : Tctxt.t) (e : Ast.exp node) : Ast.ty =
  begin match e.elt with
    | CNull ref -> 
      if ((typecheck_ty e c (TRef ref)) = ()) then TNullRef ref else type_error e "invalid reference type"
    | CBool b -> TBool
    | CInt i -> TInt
    | CStr s -> TRef (RString)
    | Id id -> 
      let local_option = lookup_local_option id c in
      begin match local_option with
        | Some t -> t
        | None -> 
          let global_option = lookup_global_option id c in
          begin match global_option with
            | Some t -> t
            | None -> type_error e "id not in context"
        end
    end
    | CArr (ty, elems) -> 
      let is_wf = ((typecheck_ty e c ty) = ()) in
      let mapped_list = List.map (typecheck_exp c) elems in 
      let weird_list = List.map (weird_function ty) mapped_list in (*[ty, ty, ..., ty]*)
      let mapped_list2 = List.map2 (subtype c) mapped_list weird_list in
      let folded_list = List.fold_left ( && ) true mapped_list2 in
      let res = folded_list && is_wf in
      if res then TRef (RArray ty) else type_error e "invalid array"
    | NewArr (ty,e1,id,e2) -> 
      let is_wf = ((typecheck_ty e c ty) = ()) in
      let is_index = ((typecheck_exp c e1) = TInt) in
      let local_option = lookup_local_option id c in
      let is_not_local = 
        begin match local_option with
          | None -> true
          | Some s -> false
      end in
      let temp_ctxt = {locals = (add_local c id TInt).locals; globals = c.globals; structs = c.structs} in
      let ty2 = typecheck_exp temp_ctxt e2 in
      let is_subtype = subtype c ty2 ty in
      let res = is_wf && is_index && is_not_local && is_subtype in
      if res then TRef (RArray ty) else type_error e "invalid array"
    | Index (e1,e2) -> 
      let e1_ty = typecheck_exp c e1 in
      let e2_ty = typecheck_exp c e2 in
      begin match e1_ty, e2_ty with
        | TRef (RArray t), TInt -> t
        | _ -> type_error e1 "invalid index expression"
    end
    | Length e1 -> 
      let e1_ty = typecheck_exp c e1 in
      begin match e1_ty with
        | TRef (RArray e1_ty) -> TInt
        | TNullRef (RArray e1_ty) -> TInt
        | _ -> type_error e "not an array"
    end
    | CStruct (id, fields) -> 
      let strct_option = lookup_struct_option id c in
      begin match strct_option with
        | None -> type_error e "struct not in context"
        | Some fields_ -> 
          if ((List.length fields) <> (List.length fields_)) then type_error e "fields do not match" else
          if (check_dups_cstruct fields) then type_error e "duplicate fields" else 
          let res = ref [] in
          for i=0 to (List.length fields - 1) do
            let id_, exp_ = List.nth fields i in
            let exp_ty = typecheck_exp c exp_ in
            let field_ty_option = lookup_field_option id id_ c in
            let is_subtype = 
            begin match field_ty_option with
              | None -> false
              | Some ty -> subtype c exp_ty ty
          end in
            res := is_subtype :: !res;
          done;
          let fold_res = List.fold_left ( && ) true !res in
          if (fold_res) then TRef (RStruct id) else type_error e "fields do not match"
    end
    | Proj (e1, fid) -> 
      let e1_ty = typecheck_exp c e1 in
      begin match e1_ty with
        | TRef (RStruct sid) | TNullRef (RStruct sid) -> 
          let struct_option = lookup_struct_option sid c in
          begin match struct_option with
            | None -> type_error e "struct not in context"
            | Some fl ->
              let field_option = lookup_field_option sid fid c in
              begin match field_option with
                | None -> type_error e "field not in context"
                | Some s -> s
            end
        end
        | _ -> type_error e "not a struct"
    end
    | Call (e1, el) -> 
      let ftype = typecheck_exp c e1 in
      begin match ftype with
        | TRef (RFun (args, ret_ty)) -> 
          if(List.length el <> List.length args) then type_error e1 "wrong number of arguments" else
          let el_types = List.map (typecheck_exp c) el in
          let subtypes_list = List.map2 (subtype c) el_types args in
          let res = List.fold_left ( && ) true subtypes_list in
          let rt = 
            begin match ret_ty with
              | RetVal t -> t
              | RetVoid -> type_error e1 "cant call void function here"
          end in
          if (res) then rt else type_error e1 "not matching argument types"
        | _ -> type_error e1 "exp1 not a function"
  end
    | Bop (binop,e1,e2) -> typecheck_binop c binop e1 e2
    | Uop (unop, e1) -> 
      let e1_ty = typecheck_exp c e1 in
      begin match unop, e1_ty with
        | Neg, TInt -> TInt
        | Bitnot, TInt -> TInt
        | Lognot, TBool -> TBool
        | _, _ -> type_error e "invalid unop type"
    end
end

and typecheck_binop (c:Tctxt.t) (b:binop) (e1:exp node) (e2:exp node): Ast.ty =
  begin match b with
    | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> 
      let e1_ty = typecheck_exp c e1 in
      let e2_ty = typecheck_exp c e2 in
      begin match e1_ty, e2_ty with 
        | TInt, TInt -> TInt
        | _, _ -> type_error e1 "invalid binop operands"
    end
    | Lt | Lte | Gt | Gte  ->
      let e1_ty = typecheck_exp c e1 in
      let e2_ty = typecheck_exp c e2 in
      begin match e1_ty, e2_ty with 
      | TInt, TInt -> TBool
      | _, _ -> type_error e1 "invalid binop operands"
    end
    | And | Or ->
      let e1_ty = typecheck_exp c e1 in
      let e2_ty = typecheck_exp c e2 in
      begin match e1_ty, e2_ty with
        | TBool, TBool -> TBool
        | _, _ -> type_error e1 "invalid binop operands"
    end
    | Eq ->
      let t1 = typecheck_exp c e1 in
      let t2 = typecheck_exp c e2 in
      if (subtype c t1 t2 && subtype c t2 t1) then TBool else type_error e1 "invalid operands for equality check"
    | Neq ->
      let t1 = typecheck_exp c e1 in
      let t2 = typecheck_exp c e2 in
      if (subtype c t1 t2 && subtype c t2 t1) then TBool else type_error e1 "invalid operands for inequality check"
end
(* statements --------------------------------------------------------------- *)

(* Typecheck a statement 
   This function should implement the statment typechecking rules from oat.pdf.  

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
let check_id_assn (tc: Tctxt.t) (id: Ast.id) : bool = 
  let local_option = lookup_local_option id tc in
  let is_local_var =
    begin match local_option with
      | None -> false
      | Some s -> true
  end in
  let global_option = lookup_global_option id tc in
  let not_global_fdecl =
    begin match global_option with
      | None -> true
      | Some s -> 
        begin match s with
          | TRef (RFun (args,rt)) -> false
          | _ -> true
      end
  end in
  (is_local_var || not_global_fdecl)

let rec get_id_rec (e: Ast.exp node) : Ast.id =
  begin match e.elt with
    | Id id -> id
    | Index (e1,e2) -> get_id_rec e1
    | Proj (e, id) -> get_id_rec e 
    | _ -> type_error e "can't get id"
end

let rec typecheck_stmt (tc : Tctxt.t) (s:Ast.stmt node) (to_ret:ret_ty) : Tctxt.t * bool =
  begin match s.elt with
    | Assn (lhs,e) -> 
      let cond = 
        begin match lhs.elt with
          | Id id -> check_id_assn tc id
          | Index (e1,e2) -> 
            begin match e1.elt with
              | Id _ | Index _ | Proj _ -> 
                let id = get_id_rec e1 in
                check_id_assn tc id
              | Call _ -> true
              | _ -> type_error s "invalid array expression for lhs"
          end
          | Proj (e,id) -> 
            let id = get_id_rec e in
            check_id_assn tc id
          | _ -> type_error s "not a lhs expression"
      end in
      let lhs_ty = typecheck_exp tc lhs in
      let e_ty = typecheck_exp tc e in
      let is_subtype = subtype tc e_ty lhs_ty in
      if (is_subtype && cond) then (tc,false) else type_error s "bad assign"
    | Decl (vdecl) -> (typecheck_vdecl tc vdecl, false)
    | Ret (e_opt) -> 
      begin match to_ret, e_opt with
        | RetVoid, None -> (tc,true)
        | RetVoid, Some s -> type_error s "cannot return value in void function"
        | RetVal t, None -> type_error s "must return a value"
        | RetVal t, Some e -> 
          let e_ty = typecheck_exp tc e in
          let is_subtype = subtype tc e_ty t in
          if (is_subtype) then (tc,true) else type_error (no_loc t) "wrong return type"
    end
    | SCall (e, el) -> 
      let e_ty = typecheck_exp tc e in
      let el_map = List.map (typecheck_exp tc) el in
      begin match e_ty with
        | TRef (RFun (args,rt)) ->
          begin match rt with
            | RetVal rval -> type_error e "should be void as return value"
            | RetVoid ->
              let is_subtypes = List.map2 (subtype tc) el_map args in
              let res = List.fold_left ( && ) true is_subtypes in
              if (res) then (tc,false) else type_error e "type mismatch"
        end
        | _ -> type_error e "not a function"
    end
    | If (e,b1, b2) -> 
      let is_bool = ((typecheck_exp tc e) = TBool) in
      let r1 = typecheck_block tc b1 to_ret in
      let r2 = typecheck_block tc b2 to_ret in
      if (not is_bool) then type_error e "not a boolean if expression" else
      (tc, r1 && r2)
    | Cast (rty,id,e,then_stmt,else_stmt) -> 
      let e_ty = typecheck_exp tc e in
      begin match e_ty with
        | TNullRef rty_ -> 
          let is_subtype = subtype_ref tc rty_ rty in
          begin match is_subtype with
            | true -> 
              let tc_ = add_local tc id (TRef rty) in
              let r1 = typecheck_block tc_ then_stmt to_ret in
              let r2 = typecheck_block tc else_stmt to_ret in
              (tc_, r1 && r2)
            | false -> type_error s "not a subtype"
        end
        | _ -> type_error s "not a nullref"
    end
    | For (vdecls, e_opt, s_opt, block) -> 
      let tc2 = typecheck_vdecls tc vdecls in
      let is_bool =
        begin match e_opt with
          | None -> true
          | Some e_ -> (typecheck_exp tc2 e_ = TBool)
      end in
      if (not is_bool) then type_error s "not a bool in for loop" else
      let _, _ = 
        begin match s_opt with
          | None -> (Tctxt.empty, false)
          | Some s_ -> typecheck_stmt tc2 s_ to_ret
      end in
      let _ = typecheck_block tc2 block to_ret in
      (tc,false)
    | While (e, sl) -> typecheck_while_stmt tc e sl to_ret     
end

and typecheck_while_stmt (tc : Tctxt.t) (e: Ast.exp node) (sl:Ast.stmt node list) (to_ret:ret_ty) : Tctxt.t * bool =
  let is_bool = ((typecheck_exp tc e) = TBool) in
  let _ = typecheck_block tc sl to_ret in
  if (not is_bool) then type_error e "not a bool in while expression" else
  (tc,false)

and typecheck_vdecl (tc : Tctxt.t) (v: Ast.vdecl) : Tctxt.t =
  begin match v with
    | (id,e) -> 
      let e_ty = typecheck_exp tc e in
      let local_option = lookup_local_option id tc in
        begin match local_option with
          | Some s -> type_error e "identifier already used"
          | None -> (add_local tc id e_ty)
      end
end

and typecheck_vdecls (tc : Tctxt.t) (vl:Ast.vdecl list) : Tctxt.t =
  let copy = tc in
  let res = ref copy in
  for i=0 to (List.length vl - 1) do
    let curr = List.nth vl i in
    res := typecheck_vdecl !res curr;
  done;
  !res

and typecheck_block (tc : Tctxt.t) (s:Ast.stmt node list) (to_ret:ret_ty) : bool = 
  let _, r = typecheck_stmts tc s to_ret in
  r

and typecheck_stmts (tc : Tctxt.t) (s:Ast.stmt node list) (to_ret:ret_ty) : Tctxt.t * bool = 
  let copy = tc in
  let res1 = ref copy in
  let res2 = ref false in
  for i=0 to (List.length s - 1) do
    let curr = List.nth s i in
    let imed1, imed2 = typecheck_stmt !res1 curr to_ret in
    if(i <> (List.length s - 1) && imed2 && ((List.length s) > 1)) then type_error curr "return in the middle of block" else
    res1 := imed1;
    res2 := imed2;
  done;
  (!res1,!res2)
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
let rec check_dups_fnc args =
  match args with
  | [] -> false
  | h::t -> (List.exists (fun x -> (snd x) = (snd h)) t) || check_dups_fnc t

let typecheck_fdecl_block (tc: Tctxt.t) (b: Ast.block) (l: 'a Ast.node) : unit = ()

let swap_pair (x,y) = (y,x)

let typecheck_fdecl (tc : Tctxt.t) (f : Ast.fdecl) (l : 'a Ast.node) : unit =
  let has_dups = check_dups_fnc f.args in
  let temp_local_ctxt = List.map swap_pair (f.args) in
  let temp_ctxt = {locals = temp_local_ctxt; globals = tc.globals; structs = tc.structs} in
  let r = typecheck_block temp_ctxt f.body f.frtyp in
  if (r && not has_dups)
  then ()
  else type_error l "invalid function"





(* creating the typchecking context ----------------------------------------- *)

(* The following functions correspond to the
   judgments that create the global typechecking context.

   create_struct_ctxt: - adds all the struct types to the struct 'S'
   context (checking to see that there are no duplicate fields

     H |-s prog ==> H'


   create_function_ctxt: - adds the the function identifiers and their
   types to the 'F' context (ensuring that there are no redeclared
   function identifiers)

     H ; G1 |-f prog ==> G2


   create_global_ctxt: - typechecks the global initializers and adds
   their identifiers to the 'G' global context

     H ; G1 |-g prog ==> G2    


   NOTE: global initializers may mention function identifiers as
   constants, but can't mention other global values *)



let create_struct_ctxt (p:Ast.prog) : Tctxt.t =
  let res = ref [] in
  for i=0 to (List.length p - 1) do
    let curr = List.nth p i in
    let list_ =
      begin match curr with
        | Gtdecl ({elt=(id,fs);_}) -> 
          if(List.mem_assoc id !res) then type_error (no_loc curr) "struct already defined" else 
          [(id,fs)]
          (*let temp_strct = {locals = []; globals = []; structs = !res} in
          if ((typecheck_tdecl temp_strct id fs (no_loc curr)) = ()) then [(id,fs)] else type_error (no_loc curr) "duplicate fields"*)
        | _ -> []
    end in
    res := list_ @ !res;
  done;
  let oat_built_in_functions = [
    ("oat_malloc", TRef (RFun ([TInt], RetVal (TRef(RArray (TInt))))));
    ("oat_alloc_array", TRef (RFun ([TInt], RetVal (TRef (RArray (TInt))))));
    (*("oat_assert_not_null", TRef(RFun ([TNullRef ???], RetVoid)));*)
    ("oat_assert_array_length", TRef (RFun ([TRef (RArray (TInt)); TInt], RetVoid)));
    ("array_of_string", TRef (RFun ([TRef (RString)], RetVal (TRef (RArray (TInt))))));
    ("string_of_array", TRef (RFun ([TRef (RArray (TInt))], RetVal (TRef (RString)))));
    ("length_of_string", TRef (RFun ([TRef (RString)], RetVal TInt)));
    ("string_of_int", TRef (RFun ([TInt], RetVal (TRef (RString)))));
    ("string_cat", TRef (RFun ([TRef (RString); TRef (RString)], RetVal (TRef (RString)))));
    ("print_string", TRef (RFun ([TRef (RString)], RetVoid)));
    ("print_int", TRef (RFun ([TInt], RetVoid)));
    ("print_bool", TRef (RFun ([TBool], RetVoid)));
  ] in
  let res_ = {locals = []; globals = oat_built_in_functions; structs = !res} in
  res_
  

let create_function_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  let copy = tc in
  let res = ref copy.globals in
  for i=0 to (List.length p - 1) do
    let curr = List.nth p i in
    let list_ =
      begin match curr with
        | Gfdecl f -> 
          let fty = typecheck_fty tc f.elt in
          if(List.mem_assoc f.elt.fname !res) then type_error (no_loc curr) "function id already used" else [(f.elt.fname,fty)]
        | _ -> []
    end in
    res := !res @ list_;
  done;
  let res_ = {locals = []; globals = !res; structs = tc.structs} in
  res_

let create_global_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  let copy = tc.globals in
  let res = ref copy in
  for i=0 to (List.length p - 1) do
    let curr = List.nth p i in
    let list_ = 
      begin match curr with
        | Gvdecl v -> 
          let id = v.elt.name in
          let gexp = v.elt.init in
          let gexp_ty = typecheck_exp tc gexp in
          if (List.mem_assoc id !res) then type_error (no_loc curr) "id already in global context" else [(id,gexp_ty)]
        | _ -> []
    end in
    res := list_ @ !res;
  done;
  let res_ = {locals = []; globals = !res; structs = tc.structs} in
  res_

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
