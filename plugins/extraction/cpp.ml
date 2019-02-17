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
      "template"; "namespace";]
    Id.Set.empty

let pp_comment s = str"// "++h 0 s++fnl ()

let pp_header_comment = function
  | None -> mt ()
  | Some com -> pp_comment com ++ fnl () ++ fnl ()

let preamble _ comment _ usf =
  pp_header_comment comment ++
  str "#include <variant>" ++ fnl () ++
  str "#include <memory>" ++ fnl () ++
  str "template<class... Ts> struct overload : Ts... { using Ts::operator()...; };" ++ fnl () ++
  str "template<class... Ts> overload(Ts...) -> overload<Ts...>;" ++ fnl () ++
  str "
template <class F>
struct y_combinator {
    F f; // the lambda will be stored here

    // a forwarding operator():
    template <class... Args>
    decltype(auto) operator()(Args&&... args) {
        // we pass ourselves to f, then the arguments.
        // the lambda should take the first argument as `auto&& recurse` or similar.
        return f(*this, std::forward<Args>(args)...);
    }
};
// helper function that deduces the type of the lambda:
template <class F>
y_combinator<std::decay_t<F>> make_y_combinator(F&& f) {
    return {std::forward<F>(f)};
}" ++ fnl ()

let pr_id id =
  str @@ String.map (fun c -> if c == '\'' then '~' else c) (Id.to_string id)

let paren = pp_par true
let brace = fun s -> str "{" ++ s ++ str "}"
let arrow = fun s -> str "<" ++ s ++ str ">"

let semicolon = fun () -> str ";"

let pp_lambda_decl st =
  let lambda_signature =
    function parameters ->
        hov 2 (str "[]" ++ (paren parameters) ++
        (brace (fnl () ++ st ++ fnl())) ++ fnl ()) and
  autoify = (fun s -> str "auto " ++ pr_id s)  in
 function
  | [] -> assert false
  | [id] -> lambda_signature (autoify id)
  | l -> lambda_signature (prlist_with_sep (fun _ -> str ",") autoify l)

let pp_apply st _ = function
  | [] -> st
  | [a] -> hov 2 (paren (st ++ spc () ++ a))
  | args -> st ++ paren (
                          (prlist_with_sep (fun x -> str ",") (fun x -> x ) args))

(*s The pretty-printer for Scheme syntax *)

let pp_global k r = str (Common.pp_global k r)

(*s Pretty-printing of expressions.  *)

let rec pp_expr env args =
  let apply st = pp_apply st true args in
  function
  | MLrel n ->
    let id = get_db_name n env in apply (pr_id id)
  | MLapp (f,args') ->
    let stl = List.map (pp_expr env []) args' in
    pp_expr env (stl @ args) f
  | MLlam _ as a ->
    let fl,a' = collect_lams a in
    let fl,env' = push_vars (List.map id_of_mlid fl) env in
    let listrevfl = List.rev fl in
    apply (pp_lambda_decl (pp_expr env' [] a') listrevfl)
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
      pp_global Cons r ++ brace (
             prlist_with_sep spc (pp_cons_args env) args')
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
      if not (is_coinductive_type typ) then pp_expr env [] t
      else paren (str "force" ++ spc () ++ pp_expr env [] t)
    in
    apply (v 3 (pp_template_typecase matched_expr env pv))
  | MLfix (i,ids,defs) ->
    let ids',env' = push_vars (List.rev (Array.to_list ids)) env in
    pp_fix env' i (Array.of_list (List.rev ids'),defs) args
  | MLexn s ->
    (* An [MLexn] may be applied, but I don't really care. *)
    paren (str "error" ++ spc () ++ qs s)
  | MLdummy _ ->
    str "__" (* An [MLdummy] may be applied, but I don't really care. *)
  | MLmagic a ->
    pp_expr env args a
  | MLaxiom -> paren (str "error \"AXIOM TO BE REALIZED\"")

and pp_cons_args env = function
  | MLcons (_,r,args) when is_coinductive r ->
    paren (pp_global Cons r ++
           (if List.is_empty args then mt () else spc ()) ++
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
        let pattern_matching_decl = str "[&]" ++ paren (cons ++ str " v") and
        variable_name = prlist_with_sep fnl (fun s -> s ++ semicolon ()) (List.mapi (fun i s->str "auto " ++ s ++ str " = *v.value") types)
      in pattern_matching_decl ++ brace (variable_name ++ str "return " ++ s2 ++ semicolon ())) in
  let overload_call = str "overload" ++ paren (prvect_with_sep (fun _ -> str "," ++ fnl ()) pattern pv) in
    str "return std::visit" ++ paren (overload_call ++ str "," ++ matched_expr) ++ semicolon ()

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

  (**
let rec json_type vl = function
  | Tmeta _ | Tvar' _ -> assert false
  | Tvar i -> (try
      let varid = List.nth vl (pred i) in json_dict [
        ("what", json_str "type:var");
        ("name", json_id varid)
      ]
    with Failure _ -> json_dict [
        ("what", json_str "type:varidx");
        ("name", json_int i)
      ])
  | Tglob (r, l) -> json_dict [
      ("what", json_str "type:glob");
      ("name", json_global Type r);
      ("args", json_list (List.map (json_type vl) l))
    ]
  | Tarr (t1,t2) -> json_dict [
      ("what", json_str "type:arrow");
      ("left", json_type vl t1);
      ("right", json_type vl t2)
    ]
  | Tdummy _ -> json_dict [("what", json_str "type:dummy")]
  | Tunknown -> json_dict [("what", json_str "type:unknown")]
  | Taxiom -> json_dict [("what", json_str "type:axiom")]
 *)

 let rec type_alias = function
  | Tmeta _ | Tvar' _ -> assert false
  | Tvar i -> str "tvar"
  | Tglob (r, l) -> pp_global Type r
  | Tarr (t1,t2) -> str "tarr"
  | Tdummy _ -> str "tdummy"
  | Tunknown -> str "tunknow"
  | Taxiom -> str "taxiom"


(** Declare a new algebraic type *)
let pp_newtype ip pl cv =
  let main_type_name = pp_global Type (IndRef ip) in
    let pp_ctor = fun idx ctor ->
      let generic_name = pp_global Cons (ConstructRef (ip, idx + 1))
      and members =
        if List.is_empty ctor
          then
            mt ()
          else
            let tmp = fun s -> s |> type_alias |> (fun s -> str "std::unique_ptr" ++ arrow s ++ str " value" ++ semicolon()) in
              prlist_with_sep fnl tmp ctor
      in generic_name, str "struct " ++ generic_name ++ brace members ++ semicolon ()
    in let subtype_name = Array.mapi pp_ctor cv in
      let forward_declaration = str "struct " ++ main_type_name ++ semicolon ()
      and constructor_declarations = prvect_with_sep fnl snd subtype_name
      and actual_decl = str "struct " ++ pp_global Type (IndRef ip) ++ (brace (str "std::variant" ++ arrow (prvect_with_sep (fun _ -> str ",") fst subtype_name) ++ str " value;")) ++ semicolon ()
      in
        forward_declaration ++ fnl () ++ constructor_declarations ++ fnl () ++  actual_decl ++ fnl()


(*s Pretty-printing of a declaration. *)

let pp_decl = function
  | Dind (kn, defs) -> prvecti_with_sep spc
      (fun i p -> if p.ip_logical then str ""
     else pp_newtype (kn, i) p.ip_vars p.ip_types) defs.ind_packets
  | Dtype _ -> mt ()
  | Dfix (rv, defs,_) ->
    let names = Array.map
        (fun r -> if is_inline_custom r then mt () else pp_global Term r) rv
    in
    prvecti
      (fun i r ->
         let void = is_inline_custom r ||
                    (not (is_custom r) &&
                     match defs.(i) with MLexn "UNUSED" -> true | _ -> false)
         in
         if void then mt ()
         else
          let fixpoint_version = str "const auto " ++ names.(i) ++ str " = make_y_combinator" ++ paren
                     (if is_custom r then str (find_custom r)
                      else pp_expr (empty_env ()) [] defs.(i)) in
           hov 2 fixpoint_version ++ semicolon () ++ fnl ())
      rv
  | Dterm (r, a, _) ->
    if is_inline_custom r then mt ()
    else
      hov 2 (str "const auto& " ++ pp_global Term r ++ spc () ++ str " = " ++
                    (if is_custom r then str (find_custom r)
                     else pp_expr (empty_env ()) [] a) ++ semicolon ())
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
