open Libsail.Ast
open Libsail.Ast_defs
open Libsail.Ast_util
open Libsail.Type_check

module Big_int = Nat_big_num
module Type_check = Libsail.Type_check
module Util = Libsail.Util
module Parse_ast = Libsail.Parse_ast
module Reporting = Libsail.Reporting

(* ==== Re-writing overloaded ASL functions ==== *)

let is_valspec = function
  | DEF_aux (DEF_val _, _) -> true
  | _ -> false

let is_fundef = function
  | DEF_aux (DEF_fundef _, _) -> true
  | _ -> false

let is_overload = function
  | DEF_aux (DEF_overload _, _) -> true
  | _ -> false

let id_append id str =
  match id with
  | Id_aux (Id v, l) -> Id_aux (Id (v ^ "__" ^ str), l)
  | Id_aux (Operator _, _) -> failwith "Cannot append to infix id"

let rename_funcl f (FCL_aux (FCL_funcl (id, pexp), annot)) =
  FCL_aux (FCL_funcl (f id, pexp), annot)

let rename_fundef f (FD_aux (FD_function (r_opt, t_opt, funcls), annot)) =
  FD_aux (FD_function (r_opt, t_opt, List.map (rename_funcl f) funcls), annot)

let rec rename_fundefs n = function
  | (DEF_aux (DEF_fundef fdef, a) :: defs) -> DEF_aux (DEF_fundef (rename_fundef (fun id -> id_append id (string_of_int n)) fdef), a) :: rename_fundefs (n + 1) defs
  | def :: defs -> def :: rename_fundefs n defs
  | [] -> []

let rename_valspec_aux f (VS_val_spec (typschm, id, ext)) = VS_val_spec (typschm, f id, ext)

let rename_valspec f (VS_aux (vs_aux, annot)) = VS_aux (rename_valspec_aux f vs_aux, annot)

let valspec_id (VS_aux (VS_val_spec (_, id, _), _)) = id

let valspec_of_def = function
  | DEF_aux (DEF_val vs, _) -> vs
  | _ -> assert false

let rec rename_valspecs n = function
  | (DEF_aux (DEF_val vs, a) :: defs) -> DEF_aux (DEF_val (rename_valspec (fun id -> id_append id (string_of_int n)) vs), a) :: rename_valspecs (n + 1) defs
  | def :: defs -> def :: rename_valspecs n defs
  | [] -> []

(*let same_effects valspecs =
  let rec valspec_effects = function
    | DEF_spec (VS_aux (VS_val_spec (TypSchm_aux (TypSchm_ts (_, Typ_aux (Typ_fn (_, _, eff), _)), _), _, _, _), _)) :: specs ->
       union_effects eff (valspec_effects specs)
    | [] -> no_effect
    | _ -> failwith "Valspec found without function type"
  in
  let rec set_effects eff = function
    | DEF_spec (VS_aux (VS_val_spec (TypSchm_aux (TypSchm_ts (typq, Typ_aux (Typ_fn (typ_f, typ_t, _), typ_annot)), ts_annot), id, ext, is_cast), vs_annot)) :: specs ->
       DEF_spec (VS_aux (VS_val_spec (TypSchm_aux (TypSchm_ts (typq, Typ_aux (Typ_fn (typ_f, typ_t, eff), typ_annot)), ts_annot), id, ext, is_cast), vs_annot))
       :: set_effects eff specs
    | [] -> []
    | _ -> failwith "Valspec found without function type"
  in
  set_effects (valspec_effects valspecs) valspecs*)

let rewrite_overloaded_top sail =
  let valspecs = List.filter is_valspec sail in
  let funs = List.filter is_fundef sail in
  let others = List.filter (fun def -> not (is_fundef def || is_valspec def || is_overload def)) sail in
  if others != [] || List.length valspecs <= 1 || List.length funs != List.length valspecs then
    sail
  else
    begin
      print_endline (Util.("Overloading" |> green |> clear));
      let id = valspec_id (valspec_of_def (List.hd valspecs)) in
      let valspecs = (*same_effects*) (rename_valspecs 0 valspecs) in
      let get_set_overload =
        if Str.string_match (Str.regexp "^a[sg]et_") (string_of_id id) 0 then
          let id = mk_id (Str.replace_first (Str.regexp "^a[sg]et_") "" (string_of_id id)) in
          [mk_def (DEF_overload (id, List.map (fun def -> valspec_id (valspec_of_def def)) valspecs))]
        else
          []
      in
      valspecs
      @ [mk_def (DEF_overload (id, List.map (fun def -> valspec_id (valspec_of_def def)) valspecs))]
      @ get_set_overload
      @ rename_fundefs 0 funs
    end

(* ==== Generic re-writing support ==== *)

(* Modify all subpatterns bottom up *)
let rec map_pat f (P_aux (p_aux, l)) =
  let rewrap p_aux = P_aux (p_aux, l) in
  match p_aux with
  | P_lit lit -> f (rewrap (P_lit lit))
  | P_wild -> f (rewrap P_wild)
  | P_as (pat, id) ->
     let p_aux = P_as (map_pat f pat, id) in
     f (rewrap p_aux)
  | P_typ (typ, pat) ->
     let p_aux = P_typ (typ, map_pat f pat) in
     f (rewrap p_aux)
  | P_id id -> f (rewrap (P_id id))
  | P_var (pat, kid) ->
     let p_aux = P_var (map_pat f pat, kid) in
     f (rewrap p_aux)
  | P_app (id, pats) ->
     let p_aux = P_app (id, List.map (map_pat f) pats) in
     f (rewrap p_aux)
  | P_vector pats ->
     let p_aux = P_vector (List.map (map_pat f) pats) in
     f (rewrap p_aux)
  | P_vector_concat pats ->
     let p_aux = P_vector_concat (List.map (map_pat f) pats) in
     f (rewrap p_aux)
  | P_tuple pats ->
     let p_aux = P_tuple (List.map (map_pat f) pats) in
     f (rewrap p_aux)
  | P_struct (fpats, fwild) ->
     let map_fpat (id, pat) = (id, map_pat f pat) in
     let p_aux = P_struct (List.map map_fpat fpats, fwild) in
     f (rewrap p_aux)
  | P_list pats ->
     let p_aux = P_list (List.map (map_pat f) pats) in
     f (rewrap p_aux)
  | P_cons (pat1, pat2) ->
     let p_aux = P_cons (map_pat f pat1, map_pat f pat2) in
     f (rewrap p_aux)
  | P_or (pat1, pat2) ->
     let p_aux = P_or (map_pat f pat1, map_pat f pat2) in
     f (rewrap p_aux)
  | P_not pat ->
     let p_aux = P_not (map_pat f pat) in
     f (rewrap p_aux)
  | P_string_append pats ->
     let p_aux = P_string_append (List.map (map_pat f) pats) in
     f (rewrap p_aux)
  | P_vector_subrange _ -> rewrap p_aux

type alg =
  { f_exp : uannot exp -> uannot exp;
    f_pat : uannot pat -> uannot pat;
    f_lexp : uannot lexp -> uannot lexp;
    f_fexp : uannot fexp -> uannot fexp;
    f_typ : typ -> typ;
  }

let id_alg =
  { f_exp = (fun x -> x);
    f_pat = (fun x -> x);
    f_lexp = (fun x -> x);
    f_fexp = (fun x -> x);
    f_typ = (fun x -> x)
  }

let rec map_exp alg (E_aux (exp_aux, l)) =
  let rewrap exp_aux = E_aux (exp_aux, l) in
  match exp_aux with
  | E_block exps ->
     let exp_aux = E_block (List.map (map_exp alg) exps) in
     alg.f_exp (rewrap exp_aux)
  | E_id id ->
     let exp_aux = E_id id in
     alg.f_exp (rewrap exp_aux)
  | E_lit lit ->
     let exp_aux = E_lit lit in
     alg.f_exp (rewrap exp_aux)
  | E_typ (typ, exp) ->
     let exp_aux = E_typ (alg.f_typ typ, map_exp alg exp) in
     alg.f_exp (rewrap exp_aux)
  | E_app (id, exps) ->
     let exp_aux = E_app (id, List.map (map_exp alg) exps) in
     alg.f_exp (rewrap exp_aux)
  | E_app_infix (exp1, id, exp2) ->
     let exp_aux = E_app_infix (map_exp alg exp1, id, map_exp alg exp2) in
     alg.f_exp (rewrap exp_aux)
  | E_tuple exps ->
     let exp_aux = E_tuple (List.map (map_exp alg) exps) in
     alg.f_exp (rewrap exp_aux)
  | E_if (exp1, exp2, exp3) ->
     let exp_aux = E_if (map_exp alg exp1, map_exp alg exp2, map_exp alg exp3) in
     alg.f_exp (rewrap exp_aux)
  | E_for (id, exp1, exp2, exp3, order, exp4) ->
     let exp_aux = E_for (id, map_exp alg exp1, map_exp alg exp2, map_exp alg exp3, order, map_exp alg exp4) in
     alg.f_exp (rewrap exp_aux)
  | E_vector exps ->
     let exp_aux = E_vector (List.map (map_exp alg) exps) in
     alg.f_exp (rewrap exp_aux)
  | E_vector_access (exp1, exp2) ->
     let exp_aux = E_vector_access (map_exp alg exp1, map_exp alg exp2) in
     alg.f_exp (rewrap exp_aux)
  | E_vector_subrange (exp1, exp2, exp3) ->
     let exp_aux = E_vector_subrange (map_exp alg exp1, map_exp alg exp2, map_exp alg exp3) in
     alg.f_exp (rewrap exp_aux)
  | E_vector_update (exp1, exp2, exp3) ->
     let exp_aux = E_vector_update (map_exp alg exp1, map_exp alg exp2, map_exp alg exp3) in
     alg.f_exp (rewrap exp_aux)
  | E_vector_update_subrange (exp1, exp2, exp3, exp4) ->
     let exp_aux = E_vector_update_subrange (map_exp alg exp1, map_exp alg exp2, map_exp alg exp3, map_exp alg exp4) in
     alg.f_exp (rewrap exp_aux)
  | E_vector_append (exp1, exp2) ->
     let exp_aux = E_vector_append (map_exp alg exp1, map_exp alg exp2) in
     alg.f_exp (rewrap exp_aux)
  | E_list exps ->
     let exp_aux = E_list (List.map (map_exp alg) exps) in
     alg.f_exp (rewrap exp_aux)
  | E_cons (exp1, exp2) ->
     let exp_aux = E_cons (map_exp alg exp1, map_exp alg exp2) in
     alg.f_exp (rewrap exp_aux)
  | E_struct fexps ->
     let exp_aux = E_struct (List.map (map_fexp alg) fexps) in
     alg.f_exp (rewrap exp_aux)
  | E_struct_update (exp, fexps) ->
     let exp_aux = E_struct_update (map_exp alg exp, List.map (map_fexp alg) fexps) in
     alg.f_exp (rewrap exp_aux)
  | E_field (exp, id) ->
     let exp_aux = E_field (map_exp alg exp, id) in
     alg.f_exp (rewrap exp_aux)
  | E_match (exp, pexps) ->
     let exp_aux = E_match (map_exp alg exp, List.map (map_pexp alg) pexps) in
     alg.f_exp (rewrap exp_aux)
  | E_var (lexp, exp, exp') ->
     let exp_aux = E_var (map_lexp alg lexp, map_exp alg exp, map_exp alg exp') in
     alg.f_exp (rewrap exp_aux)
  | E_let (letbind, exp) ->
     let exp_aux = E_let (map_letbind alg letbind, map_exp alg exp) in
     alg.f_exp (rewrap exp_aux)
  | E_assign (lexp, exp) ->
     let exp_aux = E_assign (map_lexp alg lexp, map_exp alg exp) in
     alg.f_exp (rewrap exp_aux)
  | E_sizeof nexp ->
     let exp_aux = E_sizeof nexp in
     alg.f_exp (rewrap exp_aux)
  | E_constraint (n_constraint) ->
     let exp_aux = E_constraint (n_constraint) in
     alg.f_exp (rewrap exp_aux)
  | E_exit exp ->
     let exp_aux = E_exit (map_exp alg exp) in
     alg.f_exp (rewrap exp_aux)
  | E_throw exp ->
     let exp_aux = E_throw (map_exp alg exp) in
     alg.f_exp (rewrap exp_aux)
  | E_try (exp, pexps) ->
     let exp_aux = E_try (map_exp alg exp, List.map (map_pexp alg) pexps) in
     alg.f_exp (rewrap exp_aux)
  | E_return exp ->
     let exp_aux = E_return (map_exp alg exp) in
     alg.f_exp (rewrap exp_aux)
  | E_assert (exp1, exp2) ->
     let exp_aux = E_assert (map_exp alg exp1, map_exp alg exp2) in
     alg.f_exp (rewrap exp_aux)
  | E_loop (loop_type, measure, exp1, exp2) ->
     let exp_aux = E_loop (loop_type, measure, map_exp alg exp1, map_exp alg exp2) in
     alg.f_exp (rewrap exp_aux)
  | _ -> failwith "Internal construct"
and map_pexp alg (Pat_aux (p_aux, l)) =
  let rewrap p_aux = Pat_aux (p_aux, l) in
  match p_aux with
  | Pat_exp (pat, exp) ->
     rewrap (Pat_exp (map_pat alg.f_pat pat, map_exp alg exp))
  | Pat_when (pat, exp1, exp2) ->
     rewrap (Pat_when (map_pat alg.f_pat pat, map_exp alg exp1, map_exp alg exp2))
and map_lexp alg (LE_aux (l_aux, l)) =
  let rewrap l_aux = LE_aux (l_aux, l) in
  match l_aux with
  | LE_id id -> alg.f_lexp (rewrap (LE_id id))
  | LE_app (id, exps) ->
     let l_aux = LE_app (id, List.map (map_exp alg) exps) in
     alg.f_lexp (rewrap l_aux)
  | LE_typ (typ, id) -> alg.f_lexp (rewrap (LE_typ (alg.f_typ typ, id)))
  | LE_tuple lexps ->
     let l_aux = LE_tuple (List.map (map_lexp alg) lexps) in
     alg.f_lexp (rewrap l_aux)
  | LE_vector (lexp, exp) ->
     let l_aux = LE_vector (map_lexp alg lexp, map_exp alg exp) in
     alg.f_lexp (rewrap l_aux)
  | LE_vector_concat lexps ->
     let l_aux = LE_vector_concat (List.map (map_lexp alg) lexps) in
     alg.f_lexp (rewrap l_aux)
  | LE_vector_range (lexp, exp1, exp2) ->
     let l_aux = LE_vector_range (map_lexp alg lexp, map_exp alg exp1, map_exp alg exp2) in
     alg.f_lexp (rewrap l_aux)
  | LE_field (lexp, id) ->
     let l_aux = LE_field (map_lexp alg lexp, id) in
     alg.f_lexp (rewrap l_aux)
  | LE_deref exp ->
     let l_aux = LE_deref (map_exp alg exp) in
     alg.f_lexp (rewrap l_aux)
and map_fexp alg (FE_aux (FE_fexp (id, exp), l)) =
  alg.f_fexp (FE_aux (FE_fexp (id, map_exp alg exp), l))
and map_letbind alg (LB_aux (LB_val (pat, exp), l)) =
  LB_aux (LB_val (map_pat alg.f_pat pat, map_exp alg exp), l)

let map_funcl f (FCL_aux (FCL_funcl (id, pexp), annot)) =
  let (pat, guard, exp, pat_annot) = destruct_pexp pexp in
  let (id, pat, guard, exp) = f id pat guard exp in
  let pexp = construct_pexp (pat, guard, exp, pat_annot) in
  FCL_aux (FCL_funcl (id, pexp), annot)

let map_funcl_exps f id pat guard exp =
  (id, pat, Option.map f guard, f exp)

let map_fundef f = function
  | DEF_aux (DEF_fundef (FD_aux (FD_function (r_opt, t_opt, funcls), annot)), a) ->
     DEF_aux (DEF_fundef (FD_aux (FD_function (r_opt, t_opt, List.map (map_funcl f) funcls), annot)), a)
  | def -> def

let map_ast f ast = { ast with defs = List.map f ast.defs }

let map_fundefs f ast = map_ast (map_fundef f) ast

let filter_ast f ast = { ast with defs = List.filter f ast.defs }

let iter_fundefs f =
  map_fundefs (fun id pat guard exp -> f id pat guard exp; (id, pat, guard, exp))

let rec lexp_bindings (LE_aux (l_aux, _)) =
  match l_aux with
  | LE_id id -> IdSet.singleton id
  | LE_typ (_, id) -> IdSet.singleton id
  | LE_tuple lexps -> List.fold_left IdSet.union IdSet.empty (List.map lexp_bindings lexps)
  | LE_vector (lexp, _) -> lexp_bindings lexp
  | LE_vector_range (lexp, _, _) -> lexp_bindings lexp
  | LE_vector_concat lexps -> List.fold_left IdSet.union IdSet.empty (List.map lexp_bindings lexps)
  | LE_field (lexp, _) -> lexp_bindings lexp
  | LE_app _ -> IdSet.empty
  | LE_deref _ -> IdSet.empty

let exp_lexp_bindings exp =
  let ids = ref IdSet.empty in
  let collect_lexps (E_aux (e_aux, _) as exp) =
    match e_aux with
    | E_assign (lexp, _) -> ids := IdSet.union !ids (lexp_bindings lexp); exp
    | _ -> exp
  in
  let _ = map_exp { id_alg with f_exp = collect_lexps } exp in
  !ids

let rec tpat_bindings (TP_aux (tp_aux, _)) =
  match tp_aux with
  | TP_wild -> IdSet.empty
  | TP_var kid -> IdSet.singleton (id_of_kid kid)
  | TP_app (_, tpats) -> List.fold_left IdSet.union IdSet.empty (List.map tpat_bindings tpats)

let rec pat_bindings (P_aux (p_aux, _)) =
  match p_aux with
  | P_as (pat, id) -> IdSet.add id (pat_bindings pat)
  | P_typ (_, pat) -> pat_bindings pat
  | P_id id -> IdSet.singleton id
  | P_var (pat, tpat) -> IdSet.union (tpat_bindings tpat (* is this right? *)) (pat_bindings pat)
  | P_cons (pat1, pat2) -> IdSet.union (pat_bindings pat1) (pat_bindings pat2)
  | P_app (_, pats) | P_vector pats | P_vector_concat pats | P_tuple pats | P_list pats ->
     List.fold_left IdSet.union IdSet.empty (List.map pat_bindings pats)
  | _ -> IdSet.empty

let exp_pat_bindings exp =
  let ids = ref IdSet.empty in
  let collect_pats pat = ids := IdSet.union !ids (pat_bindings pat); pat in
  let _ = map_exp { id_alg with f_pat = collect_pats } exp in
  !ids

let exp_ids exp =
  let ids = ref IdSet.empty in
  let collect_id (E_aux (e_aux, _) as exp) =
    match e_aux with
    | E_id id -> (ids := IdSet.add id !ids; exp)
    | _ -> exp
  in
  let _ = map_exp { id_alg with f_exp = collect_id } exp in
  !ids

(* In ASL functions are allowed to modify their paramemters, wheras in
   Sail they are not. If a translated function attempts this, we
   introduce an additional mutable variable which is initialised with
   the value of the function argument (which gets __arg) appended *)

let rewrite_mutated_parameters =
  let id_lexp id =
    match string_of_id id with
    | "wback" | "hwupdatewalk" -> mk_lexp (LE_typ (bool_typ, id))
    | "a" | "t" -> mk_lexp (LE_typ (int_typ, id))
    | "n" -> mk_lexp (LE_typ (range_typ (nint 0) (nint 31), id))
    | _ -> mk_lexp (LE_id id)
  in

  let rewrite_funcl id pat guard exp =
    let mutated_params = IdSet.inter (pat_bindings pat) (exp_lexp_bindings exp) in
    if IdSet.is_empty mutated_params
    then (id, pat, guard, exp)
    else
      begin
        let rewrite_arg_names (P_aux (p_aux, l)) =
          match p_aux with
          | P_id id when IdSet.mem id mutated_params -> P_aux (P_id (id_append id "arg"), l)
          | _ -> P_aux (p_aux, l)
        in
        let assignments =
          List.map (fun id -> mk_exp (E_assign (id_lexp id, mk_exp (E_id (id_append id "arg")))))
                   (IdSet.elements mutated_params)
        in
        let rewrite_exp (E_aux (e_aux, l) as exp) =
          match e_aux with
          | E_block exps -> E_aux (E_block (assignments @ exps), l)
          | _ -> E_aux (E_block (assignments @ [exp]), l)
        in
        let pat = map_pat rewrite_arg_names pat in
        (id, map_pat rewrite_arg_names pat, Option.map rewrite_exp guard, rewrite_exp exp)
      end
  in
  map_fundefs rewrite_funcl

(* This rewrite turns datasize arguments from int arguments into exact
   values of the form [:'datasize:], as well as other similar
   arguments such as destsize. It also adds sensible constraints to
   funcl bodies regarding these arguments, e.g. that 'datasize is
   some small power of two *)

let map_valspec f = function
  | DEF_aux (DEF_val vs, a) -> DEF_aux (DEF_val (f vs), a)
  | def -> def

let map_valspecs f = map_ast (map_valspec f)

let map_valspec_typschm f (VS_aux (VS_val_spec (typschm, id, ext), l)) =
  VS_aux (VS_val_spec (f id typschm, id, ext), l)

let find_pat_index id pats =
  let rec find_pat_index' n id = function
    | [] -> raise Not_found
    | (P_aux (P_id id', _) :: _) when Id.compare id id' == 0 -> n
    | (_ :: pats) -> find_pat_index' (n + 1) id pats
  in
  find_pat_index' 0 id pats

let typq_append typq qis =
  match typq with
  | TypQ_aux (TypQ_no_forall, l) -> TypQ_aux (TypQ_tq qis, l)
  | TypQ_aux (TypQ_tq qis', l) -> TypQ_aux (TypQ_tq (qis' @ qis), l)

let rec replace n y = function
  | [] -> []
  | (_ :: xs) when n == 0 -> y :: xs
  | (x :: xs) -> x :: replace (n - 1) y xs

let rec rewrite_nexp_id id nexp (Nexp_aux (n_aux, l)) =
  let rewrap n_aux = Nexp_aux (n_aux, l) in
  match n_aux with
  | Nexp_id id' when Id.compare id id' == 0 -> nexp
  | Nexp_id id' -> rewrap (Nexp_id id')
  | Nexp_times (n1, n2) -> rewrap (Nexp_times (rewrite_nexp_id id nexp n1, rewrite_nexp_id id nexp n2))
  | Nexp_sum (n1, n2) -> rewrap (Nexp_sum (rewrite_nexp_id id nexp n1, rewrite_nexp_id id nexp n2))
  | Nexp_minus (n1, n2) -> rewrap (Nexp_minus (rewrite_nexp_id id nexp n1, rewrite_nexp_id id nexp n2))
  | Nexp_exp n -> rewrap (Nexp_neg (rewrite_nexp_id id nexp n))
  | Nexp_neg n -> rewrap (Nexp_neg (rewrite_nexp_id id nexp n))
  | Nexp_var kid -> rewrap (Nexp_var kid)
  | Nexp_constant c -> rewrap (Nexp_constant c)
  | Nexp_app (f, args) -> rewrap (Nexp_app (f, List.map (rewrite_nexp_id id nexp) args))

let rec rewrite_typ_nexp f (Typ_aux (t_aux, l)) =
  let rewrap t_aux = Typ_aux (t_aux, l) in
  match t_aux with
  | Typ_id id -> rewrap (Typ_id id)
  | Typ_var kid -> rewrap (Typ_var kid)
  | Typ_fn (arg_typs, ret_typ) -> rewrap (Typ_fn (List.map (rewrite_typ_nexp f) arg_typs, rewrite_typ_nexp f ret_typ))
  | Typ_tuple typs -> rewrap (Typ_tuple (List.map (rewrite_typ_nexp f) typs))
  | Typ_app (id, args) -> rewrap (Typ_app (id, List.map (rewrite_typ_arg_nexp f) args))
  | Typ_exist (kids, nc, typ) -> rewrap (Typ_exist (kids, nc, rewrite_typ_nexp f typ))
  | Typ_internal_unknown | Typ_bidir _ -> rewrap t_aux
and rewrite_typ_arg_nexp f (A_aux (ta_aux, l)) =
  let rewrap ta_aux = A_aux (ta_aux, l) in
  match ta_aux with
  | A_nexp n -> rewrap (A_nexp (f n))
  | A_typ typ -> rewrap (A_typ (rewrite_typ_nexp f typ))
  | A_order o -> rewrap (A_order o)
  | A_bool nc -> rewrap (A_bool (rewrite_nconstraint_nexp f nc))
and rewrite_nconstraint_nexp f (NC_aux (nc_aux, l)) =
  let rewrap nc_aux = NC_aux (nc_aux, l) in
  let recur nc = rewrite_nconstraint_nexp f nc in
  match nc_aux with
  | NC_equal (nexp1, nexp2) -> rewrap (NC_equal (f nexp1, f nexp2))
  | NC_bounded_ge (nexp1, nexp2) -> rewrap (NC_bounded_ge (f nexp1, f nexp2))
  | NC_bounded_gt (nexp1, nexp2) -> rewrap (NC_bounded_gt (f nexp1, f nexp2))
  | NC_bounded_le (nexp1, nexp2) -> rewrap (NC_bounded_le (f nexp1, f nexp2))
  | NC_bounded_lt (nexp1, nexp2) -> rewrap (NC_bounded_lt (f nexp1, f nexp2))
  | NC_not_equal (nexp1, nexp2) -> rewrap (NC_not_equal (f nexp1, f nexp2))
  | NC_set (kid, is) -> rewrap (NC_set (kid, is))
  | NC_or (nc1, nc2) -> rewrap (NC_or (recur nc1, recur nc2))
  | NC_and (nc1, nc2) -> rewrap (NC_and (recur nc1, recur nc2))
  | NC_app (id, args) -> rewrap (NC_app (id, List.map (rewrite_typ_arg_nexp f) args))
  | NC_var kid -> rewrap (NC_var kid)
  | NC_true -> rewrap (NC_true)
  | NC_false -> rewrap (NC_false)

(* Rewriting datasize variables in the decode functions *)

let int_leaves exp =
  let rec ints (E_aux (e_aux, _)) =
    match e_aux with
    | E_if (_exp1, exp2, exp3) -> ints exp2 @ ints exp3
    | E_lit (L_aux (L_num n, _)) -> [n]
    | _ -> raise Exit
  in
  try Some (ints exp) with
  | Exit -> None

let rewrite_int_select id defs =
  let rec rewrite_block = function
    | (E_aux (E_assign (LE_aux (LE_typ (_, id'), _), exp), _) as assignment :: exps)
         when Id.compare id id' == 0 ->
       begin
         match int_leaves exp with
           (*
         | Some [int] ->
            let lb = mk_letbind (mk_pat (P_typ (atom_typ (nconstant int), mk_pat (P_var (kid_of_id id))))) exp in
            [mk_exp (E_let (lb, mk_exp (E_block exps)))]
            *)
         | Some ints ->
            let existential = exist_typ (exp_loc assignment) (fun kid -> nc_set kid ints) (fun kid -> atom_typ (nvar kid)) in
            let lb = mk_letbind (mk_pat (P_typ (existential, mk_pat (P_var (mk_pat (P_id id), mk_typ_pat (TP_var (kid_of_id id))))))) exp in
            [mk_exp (E_let (lb, mk_exp (E_block exps)))]
         | None -> assignment :: exps
       end
    | exp :: exps -> exp :: rewrite_block exps
    | [] -> []
  in

  let rewrite_exp (E_aux (e_aux, l) as exp) =
    match e_aux with
    | E_block exps -> E_aux (E_block (rewrite_block exps), l)
    | _ -> exp
  in
  let map_exps = map_exp { id_alg with f_exp = rewrite_exp } in
  map_fundefs (map_funcl_exps map_exps) defs

let rewrite_pointless_block_return defs =
  let rewrite_block = function
    | (E_aux (E_assign _, _) as assignment)
      :: E_aux (E_return (E_aux (E_lit (L_aux (L_unit, _)), _)), _)
      :: [] ->
       [assignment]
    | exps -> exps
  in

  let rewrite_exp (E_aux (e_aux, l) as exp) =
    match e_aux with
    | E_block exps -> E_aux (E_block (rewrite_block exps), l)
    | _ -> exp
  in
  let map_exps = map_exp { id_alg with f_exp = rewrite_exp } in
  map_fundefs (map_funcl_exps map_exps) defs

(* variables set by match statements *)

let rec is_undefined (E_aux (aux, _)) =
  match aux with
  | E_lit (L_aux (L_undef, _)) -> true
  | E_typ (_, exp) -> is_undefined exp
  | _ -> false

let lexp_id (LE_aux (aux, _)) =
  match aux with
  | LE_typ (_, id) -> Some id
  | LE_id id -> Some id
  | _ -> None

let eventually_constant defs =
  let rec is_assigning_exp id (E_aux (aux, _)) =
    match aux with
    | E_block exps -> List.exists (is_assigning_exp id) exps
    | E_assign (lexp, _) ->
       begin match lexp_id lexp with
       | Some id' -> Id.compare id id' = 0
       | None -> false
       end
    | E_throw _ -> true
    | _ -> false
  in
  let is_assigning_pexp id (Pat_aux (aux, _)) =
    match aux with
    | Pat_when (_, _, exp) | Pat_exp (_, exp) ->
       is_assigning_exp id exp
  in
  let is_assigning_match id (E_aux (aux, _)) =
    match aux with
    | E_match (_, pexps) -> List.for_all (is_assigning_pexp id) pexps
    | _ -> false
  in

  let rec split_if_chain id = function
    | E_aux (E_if (_, then_exp, E_aux (E_lit (L_aux (L_unit, _)), _)), _) as first :: rest
         when is_assigning_exp id then_exp ->
       let ifs, rest = split_if_chain id rest in
       first :: ifs, rest
    | rest -> ([], rest)
  in

  let rec rewrite_block_0 = function
    | [] -> []
    | (E_aux (E_assign (lexp, rexp), _) as assignment) :: rest
         when is_undefined rexp ->
       begin match lexp_id lexp with
       | None -> assignment :: rewrite_block_0 rest
       | Some id ->
          assignment :: rewrite_block_0 (rewrite_block_1 id rest)
       end
    | exp :: exps -> exp :: rewrite_block_0 exps
  and rewrite_block_1 id = function
    | [E_aux (E_let (lb, E_aux (E_block exps, _)), _)] ->
       [mk_exp (E_let (lb, mk_exp (E_block (rewrite_block_1 id exps))))]
    | exp :: exps when is_assigning_match id exp ->
       let future_writes = List.fold_left IdSet.union IdSet.empty (List.map exp_lexp_bindings exps) in
       let future_bindings = List.fold_left IdSet.union IdSet.empty (List.map exp_pat_bindings exps) in
       if not (IdSet.mem id future_writes || IdSet.mem id future_bindings) then
         begin
           exp :: [mk_exp (E_let (mk_letbind (mk_pat (P_id id)) (mk_exp (E_id id)), mk_exp (E_block exps)))]
         end
       else
         exp :: exps
    | exps ->
       match split_if_chain id exps with
       | [], [] -> []
       | [], exp :: exps ->
          exp :: rewrite_block_1 id exps
       | assignment_ifs, exps ->
          let future_writes = List.fold_left IdSet.union IdSet.empty (List.map exp_lexp_bindings exps) in
          let future_bindings = List.fold_left IdSet.union IdSet.empty (List.map exp_pat_bindings exps) in
          if not (IdSet.mem id future_writes || IdSet.mem id future_bindings) then
            begin
              assignment_ifs @ [mk_exp (E_let (mk_letbind (mk_pat (P_id id)) (mk_exp (E_id id)), mk_exp (E_block exps)))]
            end
          else
            assignment_ifs @ exps
  in

  let rewrite_exp (E_aux (e_aux, l) as exp) =
    match e_aux with
    | E_block exps -> E_aux (E_block (rewrite_block_0 exps), l)
    | _ -> exp
  in
  let map_exps = map_exp { id_alg with f_exp = rewrite_exp } in
  map_fundefs (map_funcl_exps map_exps) defs

(* Rewrite problematic vector expressions *)

let vector_exps defs =
  let is_constant = function
    | E_aux (E_lit _,_) -> true
    | _ -> false
  in

  let rewrite_exp (E_aux (e_aux, a) as exp) =
    let rewrap e_aux = E_aux (e_aux, a) in
    match e_aux with
    (* | E_app (Id_aux (Id "UInt", _), [E_aux (E_vector_subrange (v, hi, lo), _)])
      when not (is_constant hi && is_constant lo) ->
       rewrap (E_app (mk_id "unsigned_subrange", [v; hi; lo])) *)
    | E_app (Id_aux (Id "IsZero", _), [E_aux (E_vector_subrange (v, hi, lo), _)])
      when not (is_constant hi && is_constant lo) ->
       rewrap (E_app (mk_id "is_zero_subrange", [v; hi; lo]))
    | E_app (Id_aux (Id "IsOnes", _), [E_aux (E_vector_subrange (v, hi, lo), _)])
      when not (is_constant hi && is_constant lo) ->
       rewrap (E_app (mk_id "is_ones_subrange", [v; hi; lo]))
    | _ -> exp
  in
  let map_exps = map_exp { id_alg with f_exp = rewrite_exp } in
  map_fundefs (map_funcl_exps map_exps) defs

(* Fixing type errors *)

let rewrite_make_unique defs =
  let rewrite_funcl funcl_id pat guard exp =
    (funcl_id, pat, Option.map (locate unique) guard, locate unique exp)
  in
  map_fundefs rewrite_funcl defs

let is_unique_in_exp n exp =
  let found = ref false in
  ignore (locate (fun l -> match l with Parse_ast.Unique (m, _) when n = m -> found := true; l | _ -> l) exp);
  !found

let is_unique_in_pexp n pexp =
  let (_, _, exp, _) = destruct_pexp pexp in
  is_unique_in_exp n exp

let rec is_flow_condition env exp = match unaux_exp exp with
  | E_constraint _ -> true
  | E_lit (L_aux (L_true, _)) | E_lit (L_aux (L_false, _)) | E_lit (L_aux (L_num _, _)) -> true
  | E_app (op, [x; y]) ->
     let funs = ["or_bool"; "and_bool"; "gteq_int"; "lteq_int"; "gt_int"; "lt_int"; "eq_int"; "neq_int"] in
     let binops = ["|"; "&"; ">="; "<="; ">"; "<"; "=="; "!="] |> List.map (fun o -> "(operator " ^ o ^ ")") in
     List.mem (string_of_id op) (funs @ binops)
     && is_flow_condition env x && is_flow_condition env y
  | E_id id ->
     begin match Env.lookup_id id env with
       | Local (Immutable, typ) ->
          begin
            try
              Option.is_some (destruct_atom_nexp env typ)
              || Option.is_some (destruct_atom_bool env typ)
            with _ -> false
          end
       | _ -> false
     end
  | _ -> false

let loc_in_exp_with_incomplete_flow_typing env n exp =
  let incomplete = ref false in
  let e_if (cond, e_then, e_else) =
    let loc_found = is_unique_in_exp n e_then || is_unique_in_exp n e_else in
    if loc_found && not (is_flow_condition env cond) then incomplete := true;
    E_if (cond, e_then, e_else)
  in
  let e_case (e, clauses) =
    if List.exists (is_unique_in_pexp n) clauses then incomplete := true;
    E_match (e, clauses)
  in
  let open Libsail.Rewriter in
  ignore (fold_exp { id_exp_alg with e_if; e_case } exp);
  !incomplete

let loc_in_pexp_with_incomplete_flow_typing env n pexp =
  let (_, _, exp, _) = destruct_pexp pexp in
  loc_in_exp_with_incomplete_flow_typing env n exp

let loc_in_funcl_with_incomplete_flow_typing env n (FCL_aux (FCL_funcl (_, pexp), _)) =
  loc_in_pexp_with_incomplete_flow_typing env n pexp

let loc_in_def_with_incomplete_flow_typing env n = function
  | DEF_aux (DEF_fundef (FD_aux (FD_function (_, _, funcls), _)), _) ->
     List.exists (loc_in_funcl_with_incomplete_flow_typing env n) funcls
  | _ -> false

(* [blocks exp] returns a list of all the E_block expressions in exp *)
let rec blocks (E_aux (aux, _) as exp) =
  match aux with
  | E_block exps ->
     exp :: List.concat (List.map blocks exps)
  | E_app (_, exps) | E_tuple exps | E_vector exps | E_list exps ->
     List.concat (List.map blocks exps)
  | E_if (cond, then_exp, else_exp) ->
     blocks cond @ blocks then_exp @ blocks else_exp
  | E_app_infix (exp1, _, exp2) | E_loop (_, _, exp1, exp2) | E_vector_access (exp1, exp2)
    | E_vector_append (exp1, exp2) | E_cons (exp1, exp2) | E_assert (exp1, exp2) | E_internal_plet (_, exp1 ,exp2) ->
     blocks exp1 @ blocks exp2
  | E_vector_subrange (exp1, exp2, exp3) | E_vector_update (exp1, exp2, exp3) ->
     blocks exp1 @ blocks exp2 @ blocks exp3
  | E_for (_, exp1, exp2, exp3, _, exp4) | E_vector_update_subrange (exp1, exp2, exp3, exp4) ->
     blocks exp1 @ blocks exp2 @ blocks exp3 @ blocks exp4
  | E_typ (_, exp) | E_internal_return exp | E_exit exp | E_throw exp | E_field (exp, _) | E_return exp | E_internal_assume (_, exp) ->
     blocks exp
  | E_assign (_, exp) ->
     blocks exp
  | E_let (lb, exp) ->
     letbind_blocks lb @ blocks exp
  | E_match (exp, cases) | E_try (exp, cases) ->
     blocks exp @ List.concat (List.map pexp_blocks cases)
  | E_var (_, exp1, exp2) ->
     blocks exp1 @ blocks exp2
  | E_id _ | E_lit _ | E_internal_value _ | E_constraint _ | E_ref _ | E_sizeof _ ->
     []
  | E_struct _ | E_struct_update _ -> []
and letbind_blocks (LB_aux (LB_val (_, exp), _)) = blocks exp
and pexp_blocks (Pat_aux (aux, _)) =
  match aux with
  | Pat_exp (_, exp) -> blocks exp
  | Pat_when (_, guard, exp) -> blocks guard @ blocks exp

(* Insert an expression into the closest block enclosing a unique location *)
let insert_into_block n insertion defs =
  let rec insert_into_exps = function
    | e :: es when is_unique_in_exp n e ->
       insertion :: e :: es
    | e :: es -> e :: insert_into_exps es
    | [] -> []
  in
  let ensure_block (E_aux (aux, annot) as exp) =
    match aux with
    | E_block _ -> exp
    | _ -> E_aux (E_block [exp], annot)
  in
  let rewrite_exp (E_aux (aux, annot) as exp) =
    match aux with
    | E_block exps ->
       let sub_blocks = List.concat (List.map blocks exps) in
       if List.exists (is_unique_in_exp n) sub_blocks then
         exp
       else if not (is_unique_in_exp n exp) then
         exp
       else
         E_aux (E_block (insert_into_exps exps), annot)
    | E_if (cond, then_exp, else_exp) ->
       let needs_block e = is_unique_in_exp n e && not (List.exists (is_unique_in_exp n) (blocks e)) in
       let then_exp' = if needs_block then_exp then ensure_block then_exp else then_exp in
       let else_exp' = if needs_block else_exp then ensure_block else_exp else else_exp in
       E_aux (E_if (cond, then_exp', else_exp'), annot)
    | _ -> exp
  in
  let map_exps = map_exp { id_alg with f_exp = rewrite_exp } in
  map_fundefs (map_funcl_exps map_exps) defs

exception Not_top_level of n_constraint;;

let rewrite_add_constraint ?(modify_val_spec=true) l env env_l nc local_ncs ast =
  (* prerr_endline "Calling rewrite_add_constraint"; *)
  match l with
  | Parse_ast.Unique (n, _) ->
     let insert_into_funbody nc =
       let assertion = mk_exp (E_assert (mk_exp (E_constraint nc), mk_lit_exp (L_string ""))) in
       insert_into_block n assertion ast;
     in
     (* We need to add a constraint for a location, so we start by
        finding the function containing that location. *)
     let function_id = ref None in
     ignore (map_fundefs (fun id pat guard exp -> if is_unique_in_exp n exp then function_id := Some id else (); (id, pat, guard, exp)) ast);

     begin match !function_id with
     | Some id ->
        let add_constraint _id (TypSchm_aux (TypSchm_ts (typq, typ), tq_l)) =
          let kopts, ncs = quant_split typq in
          let conjs = constraint_conj (constraint_simp nc) in
          let open Type_check in
          (* We want to remove any conjunct in the constraint we are
             adding that is derivable from existing constraints, so as
             to not duplicate constraints in the type signature. *)
          let env = Env.add_typquant tq_l typq env in
          let conjs = List.filter (fun conj -> not (prove __POS__ env_l conj ||
                                                      (KidSet.for_all (fun tyvar -> Env.shadows tyvar env_l == 0) (tyvars_of_constraint conj) &&
                                                 prove __POS__ env conj))) conjs in
          (* Any constraint in local_ncs that cannot be derived by the
             function quantifer must have been introduced via flow
             typing. *)
          let flows = List.map nc_not (List.filter (fun nc -> not (prove __POS__ env nc)) local_ncs) in
          let flows =
            List.filter (fun nc -> KidSet.subset (tyvars_of_constraint nc) (KidSet.of_list (List.map kopt_kid kopts))) flows
          in
          (* prerr_endline ("Flows: " ^ Util.string_of_list ", " string_of_n_constraint flows); *)
          match conjs with
          | conj :: conjs ->
             let nc = List.fold_left nc_and conj conjs in
             let nc = List.fold_left nc_or nc flows in
             let nc_tyvars = tyvars_of_constraint nc in
             (* We can only add a constraint to the valspec if it
                contains only variables defined by that valspec. *)
             if KOptSet.subset (kopts_of_constraint nc) (KOptSet.of_list kopts)
                && KidSet.for_all (fun tyvar -> Env.shadows tyvar env_l == 0) nc_tyvars
                && List.length (quant_items typq) > 0 then
               (* Now that we are adding a constraint to the val-spec,
                  double-check whether it makes some of the existing constraints redundant *)
               let env_nc = Env.add_constraint nc (List.fold_right (Env.add_typ_var l) kopts env) in
               let nc_needed nc = try not (prove __POS__ env_nc nc) with _ -> true in
               let ncs = List.filter nc_needed (List.concat (List.map constraint_conj ncs)) in
               let qis = List.map mk_qi_kopt kopts @ List.map mk_qi_nc (ncs @ [nc]) in
               mk_typschm (mk_typquant qis) typ
             else
               raise (Not_top_level nc)
          | [] ->
             mk_typschm typq typ
        in
        begin try
            let is_spec_of_id = function
              | DEF_aux (DEF_val vs, _) -> Id.compare (id_of_val_spec vs) id = 0
              | _ -> false
            in
            (* Check whether the location with the missing constraint is nested
               under a potentially incomplete flow mapping, in which case we
               should not attach the constraint to the val-spec. *)
            let incomplete_flows = List.exists (loc_in_def_with_incomplete_flow_typing env_l n) ast.defs in

            if List.exists is_spec_of_id ast.defs && modify_val_spec && not incomplete_flows then
              map_valspecs (map_valspec_typschm add_constraint) ast
            else
              insert_into_funbody nc
          with
            Not_top_level nc -> insert_into_funbody nc
        end

     | _ -> failwith "Could not find function containing location"
     end

  | _ -> failwith ("Location must be unique" ^ Reporting.loc_to_string l)
