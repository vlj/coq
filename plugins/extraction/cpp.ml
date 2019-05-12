(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*s Production of Scheme syntax. *)

open Pp
open CErrors
open Util
open Names
open Miniml
open Mlutil
open Table
open Common

(*s Scheme renaming issues. *)

let keywords =
  List.fold_right (fun s -> Id.Set.add (Id.of_string s))
    [ "struct"; "class"; "return"; "typedef"; "using";
      "template"; "namespace"; "bool"; "int"; "default"]
    Id.Set.empty

let pp_comment s = str"// "++h 0 s++fnl ()

let pp_header_comment = function
  | None -> mt ()
  | Some com -> pp_comment com ++ fnl () ++ fnl ()

let preamble _ comment _ usf =
  pp_header_comment comment ++
  str "#include <variant>" ++ fnl () ++
  str "#include <memory>" ++ fnl () ++
  str "#include <functional>" ++ fnl () ++
  str "#include <any>" ++ fnl () ++
  str "template<class... Ts> struct overload : Ts... {" ++ fnl() ++
  str "    overload(const Ts&... ts) : Ts(ts)... {}" ++ fnl () ++
  str "    using Ts::operator()...;" ++ fnl () ++
  str "};" ++ fnl () ++
  str "
template <class F>
struct y_combinator {
    F f; // the lambda will be stored here

    // a forwarding operator():
    template <class... Args>
    decltype(auto) operator()(Args&&... args) const {
        // we pass ourselves to f, then the arguments.
        // the lambda should take the first argument as `auto&& recurse` or similar.
        return f(*this)(std::forward<Args>(args)...);
    }
};
// helper function that deduces the type of the lambda:
template <class F>
y_combinator<std::decay_t<F>> make_y_combinator(F&& f) {
    return {std::forward<F>(f)};
}" ++ fnl ()

let pp_tvar id = str (Id.to_string id)
let pr_id id =
  str @@ String.map (fun c -> if c == '\'' then '~' else c) (Id.to_string id)

let paren = pp_par true
let brace = fun s -> str "{" ++ s ++ str "}"
let arrow = fun s -> str "<" ++ s ++ str ">"

let colon = fun () -> str ","
let semicolon = fun () -> str ";"


let mt_if_empty englobing_code_function = fun lst ->
  if List.is_empty lst then mt () else englobing_code_function lst

let pp_lambda_decl st =
  let lambda_signature =
    function parameters ->
      str "[=]" ++ (paren parameters) and
  lambda_body = ((fnl () ++ str "return " ++ st ++ semicolon () |> v 1) ++ fnl() |> brace) and
  autoify = (fun s -> str "auto " ++ pr_id s)  in
  function
  | [] -> assert false
  | [id] -> lambda_signature (autoify id) ++ lambda_body
  | l -> lambda_signature (prlist_with_sep colon autoify l) ++ lambda_body

let pp_apply st _ = function lst -> st ++ prlist paren lst

(*s The pretty-printer for Scheme syntax *)

let pp_global k r = str (Common.pp_global k r)

let rec type_alias tvar_name = function
  | Tmeta _ -> str "META"
  | Tvar' _ -> str "TVAR'"
  | Tvar i -> (try pp_tvar (List.nth tvar_name (pred i)) with  _ -> str "ERROR")
  | Tglob (r, l) -> pp_global Type r ++ ((prlist_with_sep colon (type_alias tvar_name) l) |> arrow)
  | Tarr (t1,t2) as e ->
    (*let rec collect_arrow lst = function
      | Tarr (t1, t2) -> collect_arrow ( t1 :: lst) t2
      | x ->  x, lst
      in
      let out, in_lst = collect_arrow [] e in *)
    str "std::function" ++ arrow (type_alias tvar_name t2 ++ paren ([t1] |> prlist_with_sep colon (type_alias tvar_name))) ++ str " "
  | Tdummy _ -> str "tdummy "
  | Tunknown -> str "std::any"
  | Taxiom -> str "taxiom "

(*s Pretty-printing of expressions.  *)

let rec pp_expr env args =
  let apply st = pp_apply st true args in
  function
  | MLrel n ->
    let id = get_db_name n env in apply (pr_id id)
  | MLapp (f,args') ->
    let stl = List.map (pp_expr env []) args' in
    pp_expr env (stl @ args) f
  | MLlam (id, body) ->
    (* let fl,a' = collect_lams a in
       let fl,env' = push_vars (List.map id_of_mlid fl) env in
       let listrevfl = List.rev fl in *)
    let id', env' = push_vars [id_of_mlid id] env in
    apply (pp_lambda_decl (pp_expr env' [] body) id')
  | MLletin (id,a1,a2) ->
    let i,env' = push_vars [id_of_mlid id] env in
    apply
      (hv 0
         (hov 2
            (paren
               (str "let " ++
                paren
                  (paren
                     (pr_id (List.hd i) ++ spc () ++ pp_expr env [] a1))
                ++ spc () ++ hov 0 (pp_expr env' [] a2)))))
  | MLglob r ->
    apply (pp_global Term r)
  | MLcons (_,r,args') ->
    assert (List.is_empty args);
    let st =
      pp_global Cons r ++ str "_ctor" ++  (prlist_with_sep colon (pp_cons_args env) args' |> paren)
    in
    if is_coinductive r then paren (str "delay " ++ st) else st
  | MLtuple _ -> user_err Pp.(str "Cannot handle tuples in Scheme yet.")
  | MLcase (_,_,pv) when not (is_regular_match pv) ->
    user_err Pp.(str "Cannot handle general patterns in Scheme yet.")
  | MLcase (_,t,pv) when is_custom_match pv ->
    let mkfun (ids,_,e) =
      if not (List.is_empty ids) then named_lams (List.rev ids) e
      else dummy_lams (ast_lift 1 e) 1
    in
    apply
      (paren
         (hov 2
            (str (find_custom_match pv) ++ fnl () ++
             prvect (fun tr -> pp_expr env [] (mkfun tr) ++ fnl ()) pv
             ++ pp_expr env [] t)))
  | MLcase (typ,t, pv) ->
    let matched_expr =
      if not (is_coinductive_type typ) then pp_expr env [] t |> fun s -> str "static_cast" ++ (type_alias [] typ |> arrow) ++ (s |> paren)
      else paren (str "force" ++ spc () ++ pp_expr env [] t)
    in
    apply (pp_template_typecase matched_expr env pv)
  | MLfix (i,ids,defs) ->
    let ids',env' = push_vars (List.rev (Array.to_list ids)) env in
    pp_fix env' i (Array.of_list (List.rev ids'),defs) args
  | MLexn s ->
    (* An [MLexn] may be applied, but I don't really care. *)
    paren (str "error" ++ spc () ++ qs s)
  | MLdummy _ ->
    str "__" (* An [MLdummy] may be applied, but I don't really care. *)
  | MLmagic a -> str "std::any" ++ (
      (pp_expr env args a) |> paren)
  | MLaxiom -> paren (str "error \"AXIOM TO BE REALIZED\"")

and pp_cons_args env = function
  | MLcons (_,r,args) when is_coinductive r ->
    paren (pp_global Cons r ++
           (mt_if_empty (fun _ -> spc()) args) ++
           prlist_with_sep spc (pp_cons_args env) args)
  | e -> pp_expr env [] e

and pp_template_parameter_list env (ids,p,t) =
  let r = match p with
    | Pusual r -> r
    | Pcons (r,l) -> r (* cf. the check [is_regular_match] above *)
    | _ -> assert false
  in
  let ids,env' = push_vars (List.rev_map id_of_mlid ids) env in
  let args =
    List.map pr_id (List.rev ids)
  in
  (pp_global Cons r), args, (pp_expr env' [] t)

and pp_template_typecase matched_expr env pv =
  let pattern = (fun x -> let cons, types, s2 = pp_template_parameter_list env x in
                  let type_specialization = mt () in
                  let pattern_matching_decl = str "[=]" ++ paren (cons ++ str " v") and
                    variable_name = prlist_with_sep fnl (fun s -> s ++ semicolon ()) (List.mapi (fun i s->str "const auto& " ++ s ++ str " = *v.value") types)
                  in pattern_matching_decl ++ brace (variable_name ++ str "return " ++ s2 ++ semicolon ())) in
  let overload_call = str "overload" ++ (
      fnl () ++
      prvect_with_sep (fun _ -> str "," ++ fnl ()) pattern pv |> v 0 |> paren

    ) in str "std::visit" ++ paren (overload_call ++ str "," ++ matched_expr ++ str ".value")

(*s names of the functions ([ids]) are already pushed in [env],
    and passed here just for convenience. *)

and pp_fix env j (ids,bl) args =
  paren
    (str "letrec " ++
     (v 0 (paren
             (prvect_with_sep fnl
                (fun (fi,ti) ->
                   paren ((pr_id fi) ++ spc () ++ (pp_expr env [] ti)))
                (Array.map2 (fun id b -> (id,b)) ids bl)) ++
           fnl () ++
           hov 2 (pp_apply (pr_id (ids.(j))) true args))))

let pp_template_parameters_decl tvar_names =
  str "template" ++ ((
      prlist_with_sep colon (fun s -> str "typename " ++ pp_tvar s) tvar_names)
      |> arrow )

let qualified_type naked_typename tvar_names =
  naked_typename ++ ((
      prlist_with_sep colon pp_tvar tvar_names)
      |> arrow )

let declare_type_as_usings tvar_names =
  prlist_with_sep fnl (fun s -> let tvar_name = pp_tvar s in str "using _" ++ tvar_name ++ str " = " ++ tvar_name ++ semicolon ()) tvar_names

let declare_constructor tvar_names (ctor_name, ctor_args) =
  let member_decl = List.mapi (fun i s -> str "std::shared_ptr" ++ arrow (type_alias tvar_names s) ++ str (" value" ^ string_of_int i) ++ semicolon()) ctor_args
  in
  pp_template_parameters_decl tvar_names ++
  str "struct " ++ ctor_name ++
  brace (
    (** using _... = ...; *)
    declare_type_as_usings tvar_names ++ prlist_with_sep fnl (fun s -> s) member_decl) ++
  semicolon ()


let declare_constructor_function naked_typename tvar_names (ctor_name, ctor_args) =
  let args = List.mapi (fun i n -> (type_alias tvar_names n, str "a" ++ (str @@ string_of_int i))) ctor_args in
  let ctor_build = qualified_type ctor_name tvar_names ++ (prlist_with_sep colon (fun (tp, name) -> str "std::make_shared" ++ arrow tp ++ paren name) args |> brace) |> brace in
  let body = str "return " ++ ctor_build ++ semicolon () |> brace
  in
  (** template<typename ...>*)
  pp_template_parameters_decl tvar_names ++
  (** type<..> *)
  qualified_type naked_typename  tvar_names ++
  (** type_ctor *)
  str " " ++ ctor_name ++ str "_ctor" ++
  (** arg lists *)
  (
    prlist_with_sep colon (fun (tp, name) -> tp ++ str " " ++ name) args |> paren
  ) ++ body

let define_variant tvar_names type_name ctors =
  pp_template_parameters_decl tvar_names ++
  str "struct " ++ type_name ++
  (
    (** using _... = ...; *)
    declare_type_as_usings tvar_names ++
    (** std::variant<...> value; *)
    str "std::variant" ++ (
      prvect_with_sep colon (fun (n, tp) -> qualified_type n tvar_names) ctors |> arrow
    ) ++ str " value" ++ semicolon () |> brace
  ) ++ semicolon ()



(** Declare a new algebraic type *)
let pp_newtype ip pl cv =
  let
    naked_typename = pp_global Type (IndRef ip) and
  constructors_with_args_array = Array.mapi (fun idx ctor -> pp_global Cons (ConstructRef (ip, idx + 1)), ctor) cv in
  let forward_declaration = pp_template_parameters_decl pl ++ str "struct " ++ naked_typename ++ semicolon ()
  and constructor_declarations = prvect_with_sep fnl (declare_constructor pl) constructors_with_args_array
  and variant_definition = define_variant pl naked_typename constructors_with_args_array
  and constructors_function = prvect_with_sep fnl (declare_constructor_function naked_typename pl) constructors_with_args_array
  in
  forward_declaration ++ fnl () ++ constructor_declarations ++ fnl () ++ variant_definition ++  fnl() ++ constructors_function ++ fnl ()


(*s Pretty-printing of a declaration. *)

let define_fixpoint = fun ref def typ ->
  let name = pp_global Term ref and
  void = is_inline_custom ref ||
         (not (is_custom ref) &&
          match def with MLexn "UNUSED" -> true | _ -> false)
  in
  if void then mt ()
  else
    let lambda_definition = (if is_custom ref then str (find_custom ref)
                             else pp_expr (empty_env ()) [] def) in
    let to_be_combined =
      str "[]" ++ paren ( str" auto " ++ name ) ++ str " -> " ++ type_alias [] typ ++
      (fnl () ++ str "return " ++ lambda_definition ++ semicolon () |> v 1 |> brace)
    in
    let fixpoint_version = str "const " ++ type_alias [] typ ++ str " " ++ name ++ str " = make_y_combinator" ++ paren to_be_combined
    in
    fixpoint_version ++ semicolon () ++ fnl ()

let define_type = fun ref def typ ->
  (** assert (List.is_empty def); *)
  str "using " ++ pp_global Type ref ++ str " = " ++ type_alias [] typ  ++ semicolon ()

let pp_decl = function
  | Dind (kn, defs) -> prvecti_with_sep spc
                         (fun i p -> if p.ip_logical then str ""
                           else pp_newtype (kn, i) p.ip_vars p.ip_types) defs.ind_packets
  | Dtype (rv, defs, typs) -> define_type rv defs typs ++ fnl ()
  | Dfix (rv, defs, typs) -> prvecti (fun i r -> define_fixpoint r defs.(i) typs.(i)) rv
  | Dterm (r, a, _) ->
    if is_inline_custom r then mt ()
    else
      str "const auto& " ++ pp_global Term r ++ str " = " ++
      (if is_custom r then str (find_custom r)
       else pp_expr (empty_env ()) [] a) ++ semicolon ()
      ++ fnl2 ()

let rec pp_structure_elem = function
  | (l,SEdecl d) -> pp_decl d
  | (l,SEmodule m) -> pp_module_expr m.ml_mod_expr
  | (l,SEmodtype m) -> mt ()
(* for the moment we simply discard module type *)

and pp_module_expr = function
  | MEstruct (mp,sel) -> prlist_strict pp_structure_elem sel
  | MEfunctor _ -> mt ()
  (* for the moment we simply discard unapplied functors *)
  | MEident _ | MEapply _ -> assert false
(* should be expanded in extract_env *)

let pp_struct =
  let pp_sel (mp,sel) =
    push_visible mp [];
    let p = prlist_strict pp_structure_elem sel in
    pop_visible (); p
  in
  prlist_strict pp_sel

let cpp_descr = {
  keywords = keywords;
  file_suffix = ".cpp";
  file_naming = file_of_modfile;
  preamble = preamble;
  pp_struct = pp_struct;
  sig_suffix = None;
  sig_preamble = (fun _ _ _ _ -> mt ());
  pp_sig = (fun _ -> mt ());
  pp_decl = pp_decl;
}
