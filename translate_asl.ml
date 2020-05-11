open Ast
open Ast_util
open LibASL.Asl_ast
open LibASL.Asl_utils

module ASL_AST   = LibASL.Asl_ast
module ASL_PP    = LibASL.Asl_parser_pp
module ASL_TC    = LibASL.Tcheck
module ASL_Utils = LibASL.Asl_utils

type lvar =
  | Owned of mut * typ
  | Shared of mut * typ

let lvar_typ = function Owned (_, typ) | Shared (_, typ) -> typ
let lvar_mut = function Owned (mut, _) | Shared (mut, _) -> mut

let lvar_is_immutable = function
  | Owned (Immutable, _) | Shared (Immutable, _) -> true
  | Owned (Mutable, _) | Shared (Mutable, _) -> false
let lvar_is_mutable lvar = not (lvar_is_immutable lvar)

let lvar_is_owned = function Owned (_, _) -> true | Shared (_, _) -> false
let lvar_is_shared lvar = not (lvar_is_owned lvar)

let own_lvar = function
  | Shared (mut, typ)
  | Owned (mut, typ) -> Owned (mut, typ)

let share_lvar = function
  | Owned (mut, typ)
  | Shared (mut, typ) -> Shared (mut, typ)

let mk_lvar typ = Owned (Mutable, typ)
let immutable_lvar = function
  | Owned (_, typ) -> Owned (Immutable, typ)
  | Shared (_, typ) -> Shared (Immutable, typ)

let name_of_ident = function
  | Ident name
  | FIdent (name, _) -> name

let add_name_prefix pre = function
  | Ident name -> Ident (pre ^ "." ^ name)
  | FIdent (name, tag) -> FIdent (pre ^ "." ^ name, tag)

module StringMap = Map.Make(String)

module Expr = struct
  type t = expr
  let compare (e1 : expr) (e2 : expr) : int =
    (* TODO Implement proper comparison... *)
    String.compare (pp_expr e1) (pp_expr e2)
end

module ExprMap = Map.Make(Expr)

type ctx = {
  tc_env : Type_check.Env.t;
  fun_constraints : Ast.n_constraint Bindings.t;
  bound_exprs : ident ExprMap.t;
  fun_args : (ASL_AST.ty * ASL_AST.ident) list;
  locals : lvar Bindings.t;
}

let fresh_counter = ref 0

let fresh_id prefix =
  let id = mk_id (prefix ^ "_" ^ string_of_int !fresh_counter) in
  fresh_counter := !fresh_counter + 1;
  id

let empty_ctx = {
  tc_env = Type_check.initial_env;
  fun_constraints = Bindings.empty;
  bound_exprs = ExprMap.empty;
  fun_args = [];
  locals = Bindings.empty;
}

module StringSet = Set.Make(String)

let builtins = StringSet.of_list [
  "eq_enum"; "ne_enum";
  "Min"; "Max"; "Abs";
  "RoundTowardsZero";
  "Zeros"; "Ones"; "IsZero"; "IsOnes"; "ZeroExtend"; "SignExtend";
  "UInt"; "SInt";
  "Replicate";
  "print"; "println";
  "__ReadMemory"; "__WriteMemory"; "__ReadRAM"; "__WriteRAM";
]

let mono_splits = ref (Bindings.empty : (ident list) Bindings.t)

let get_mono_splits id =
  Util.option_default [] (Bindings.find_opt id !mono_splits)

let read_mono_splits_file filename =
  let file = open_in filename in
  let rec read_lines () =
    match input_line file with
    | l ->
       begin match String.split_on_char ' ' l with
         | [id; vars] ->
            let id = Ident id in
            let vars =
              get_mono_splits id
              @ List.map (fun v -> Ident v) (String.split_on_char ',' vars)
            in
            mono_splits := Bindings.add id vars !mono_splits
         | [] -> ()
         | _ -> failwith ("Failed to parse mono splits in line " ^ l)
       end;
       read_lines ()
    | exception End_of_file -> ()
  in
  read_lines ();
  close_in file

(* ASL allows arbitrary expressions in types, including calls to effectful
   functions.  We've only seen the latter used so far for getter functions
   VL_read and PL_read, reading the vector length used by the SVE extension
   from registers.  If these are used in a function, we pull them out into
   let-bindings of the form

     let 'VL = VL_read() in ...

   which allows us to use 'VL in Sail types.  Note that this assumes that
   the value of VL and PL stay constant throughout the execution of
   instructions that use them, which seems to be the intention.
 *)

let vl_read_id = ASL_AST.FIdent("VL.read", 0)
let pl_read_id = ASL_AST.FIdent("PL.read", 0)
let pl_of_vl_id = ASL_AST.Ident("PL_of_VL")

let is_vl_read = function
  | Expr_TApply (FIdent ("VL.read", _), _, _) -> true
  | _ -> false

let is_pl_read = function
  | Expr_TApply (FIdent ("PL.read", _), _, _) -> true
  | Expr_TApply (pl_of_vl, _, [vl]) ->
     Id.compare pl_of_vl pl_of_vl_id = 0 && (is_vl_read vl || vl = Expr_Var (Ident "VL"))
  | _ -> false

(* In order to support the Sail bitvector length monomorphisation for
   the prover backends, we support an optional pre-monomorphisation of
   instructions that use VL or PL, inserting a case split into the
   different supported values in the decode clause.  This can be enabled
   using the -mono_vl command line option, and the set of supported
   values for VL can be overriden using the -implemented_vls option
   (defaults to multiples of 128 up to 2048). *)

let mono_vl = ref false

let implemented_vls = ref [
  128; 256; 384; 512; 640; 768; 896; 1024;
  1152; 1280; 1408; 1536; 1664; 1792; 1920; 2048
]

let vl_expr bind_ariths expr = match expr with
  | Expr_TApply (mul_int, _, [var; Expr_LitInt i])
    when bind_ariths && name_of_ident mul_int = "mul_int" && (is_vl_read var || is_pl_read var) ->
     let var = if is_pl_read var then "PL" else "VL" in
     let var' = var ^ "_mul_" ^ i in
     let nexp = ntimes (nvar (mk_kid var)) (nconstant (Big_int.of_string i)) in
     let nc = nc_eq (nvar (mk_kid var')) nexp in
     Some (Ident var', expr, nc)
  | Expr_TApply (div_int, _, [var; Expr_LitInt i])
    when bind_ariths && name_of_ident div_int = "fdiv_int" && (is_vl_read var || is_pl_read var) ->
     let var = if is_pl_read var then "PL" else "VL" in
     let var' = var ^ "_div_" ^ i in
     let nexp = napp (mk_id "div") [nvar (mk_kid var); nconstant (Big_int.of_string i)] in
     let nc = nc_eq (nvar (mk_kid var')) nexp in
     Some (Ident var', expr, nc)
  | _ when is_vl_read expr ->
     let nc = mk_nc (NC_app (mk_id "is_VL", [arg_nexp (nvar (mk_kid "VL"))])) in
     Some (Ident "VL", expr, nc)
  | _ when is_pl_read expr ->
     let nc = mk_nc (NC_app (mk_id "is_PL", [arg_nexp (nvar (mk_kid "PL"))])) in
     Some (Ident "PL", expr, nc)
  | Expr_TApply (f, _, [vl]) when Id.compare f pl_of_vl_id = 0 && is_vl_read vl ->
     let nc = nc_eq (nvar (mk_kid "PL")) (napp (mk_id "div") [nvar (mk_kid "VL"); nint 8]) in
     let expr = Expr_TApply (pl_of_vl_id, [], [Expr_Var (Ident "VL")]) in
     Some (Ident "PL", expr, nc)
  | _ -> None

class vlExprsClass bind_ariths = object
  inherit LibASL.Asl_visitor.nopAslVisitor

  val mutable vl_exprs = ExprMap.empty
  method result = vl_exprs
  method! vexpr expr =
    match vl_expr bind_ariths expr with
    | Some (id, expr', nc) ->
       vl_exprs <- ExprMap.add expr (id, expr', nc) vl_exprs;
       DoChildren
    | None -> DoChildren
end

let vl_exprs_of_stmts bind_ariths stmts =
  (* Collect occurences of VL and related expressions, making sure that
     VL itself is the first in the list *)
  let open LibASL.Asl_visitor in
  (* let rewrite_pl = IdentSet.mem vl_read_id (calls_of_stmts stmts) in *)
  let vls = new vlExprsClass bind_ariths in
  ignore (visit_stmts (vls :> aslVisitor) stmts);
  ExprMap.bindings vls#result
  |> List.map (fun (key, (id, expr, nc)) -> (key, id, expr, nc))
  |> List.partition (fun (_, id, _, _) -> name_of_ident id = "VL")
  |> fun (vl, others) -> vl @ others

class replaceExprClass (replace: expr -> expr option) = object
    inherit LibASL.Asl_visitor.nopAslVisitor
    method! vexpr x =
        (match replace x with
        | Some r -> ChangeTo r
        | None -> DoChildren
        )
end

let rewrite_pl stmts =
  let rewrite expr =
    if is_pl_read expr then
      Some (Expr_TApply (pl_of_vl_id, [], [Expr_TApply (vl_read_id, [], [])]))
    else None
  in
  let re = new replaceExprClass rewrite in
  LibASL.Asl_visitor.visit_stmts re stmts

let subst_vl vl stmts =
  let rewrite expr =
    let pl = vl / 8 in
    if is_vl_read expr then Some (Expr_LitInt (string_of_int vl)) else
    if is_pl_read expr then Some (Expr_LitInt (string_of_int pl)) else
    match expr with
    | Expr_TApply (f, _, [vl]) when Id.compare f pl_of_vl_id = 0 ->
       if is_vl_read vl || vl = Expr_Var (Ident "VL") then
         Some (Expr_LitInt (string_of_int pl))
       else None
    | _ -> None
  in
  let re = new replaceExprClass rewrite in
  LibASL.Asl_visitor.visit_stmts re stmts

let subst_stmts (s: expr Bindings.t) stmts =
  let subst = new substClass s in
  LibASL.Asl_visitor.visit_stmts subst stmts

let is_getter id =
  let name = name_of_ident id in
  let len = String.length name in
  (len > 5 && String.sub name (len - 5) 5 = ".read")

class callsInTypesClass = object
  inherit LibASL.Asl_visitor.nopAslVisitor

  val mutable calls = ASL_Utils.IdentSet.empty
  method result = calls
  method! vtype ty =
    let open LibASL.Asl_visitor in
    let fcs = new ASL_Utils.callsClass in
    ignore (visit_type (fcs :> aslVisitor) ty);
    calls <- ASL_Utils.IdentSet.union calls fcs#result;
    DoChildren
end

let funcalls_in_types_of_stmts stmts =
  let open LibASL.Asl_visitor in
  let fcs = new callsInTypesClass in
  ignore (visit_stmts (fcs :> aslVisitor) stmts);
  fcs#result

let merge_bindings b1 b2 =
  let merge _ x y = Some y in
  ASL_Utils.Bindings.union merge b1 b2

let arg_of_ifield (IField_Field (id, _, wd)) =
  (ASL_TC.type_bits (Expr_LitInt (string_of_int wd)), id)

let locals_of_encoding = function
  | Encoding_Block (_, _, fields, _, _, _, stmts, _) ->
     let add_field bs f =
       let (ty, id) = arg_of_ifield f in
       ASL_Utils.Bindings.add id ty bs
     in
     List.fold_left add_field (ASL_Utils.locals_of_stmts stmts) fields


class replaceStmtClass (replace: stmt -> stmt option) = object
    inherit LibASL.Asl_visitor.nopAslVisitor
    method! vstmt x =
        (match replace x with
        | Some r -> ChangeTo r
        | None -> SkipChildren
        )
end

let get_asl_sfuntype (id : ident) : ASL_TC.sfuntype option =
  let sfts = ASL_TC.GlobalEnv.getSetterFun ASL_TC.env0 (stripTag id) in
  List.find_opt (fun ft -> Id.compare (ASL_TC.sft_id ft) id = 0) sfts

let get_asl_funtype (id : ident) : ASL_TC.funtype option =
  let fts = ASL_TC.GlobalEnv.getFuns ASL_TC.env0 (stripTag id) in
  match List.find_opt (fun ft -> Id.compare (ASL_TC.ft_id ft) id = 0) fts with
  | Some ft -> Some ft
  | None -> Util.option_map ASL_TC.funtype_of_sfuntype (get_asl_sfuntype id)

let instantiate_fun_ret_typ (id : ASL_AST.ident) (tes : ASL_AST.expr list) =
  match get_asl_funtype id with
  | Some (_, _, tvs, _, _, rty) when List.length tvs = List.length tes ->
     let bind_tv subst tv e = Bindings.add tv e subst in
     let subst = List.fold_left2 bind_tv Bindings.empty tvs tes in
     Some (subst_type subst rty)
  | _ -> None

let instantiate_sfun_vtyp (id : ASL_AST.ident) (tes : ASL_AST.expr list) =
  match get_asl_sfuntype id with
  | Some (_, tvs, _, _, vty) when List.length tvs = List.length tes ->
     let bind_tv subst tv e = Bindings.add tv e subst in
     let subst = List.fold_left2 bind_tv Bindings.empty tvs tes in
     Some (subst_type subst vty)
  | _ -> None

(* Collect variables that are used in slice expressions, or in arguments to
   getter and setter functions.  These typically need to be constrained to
   be within certain bounds. *)
class sliceVarsClass = object
  inherit LibASL.Asl_visitor.nopAslVisitor

  val mutable ids = ASL_Utils.IdentSet.empty
  method result = ids
  method! vslice = function
    | Slice_HiLo (expr1, expr2) | Slice_LoWd (expr1, expr2) ->
       let ids1 = fv_expr expr1 in
       let ids2 = fv_expr expr2 in
       ids <- IdentSet.union ids (IdentSet.union ids1 ids2);
       DoChildren
    | Slice_Single (expr) ->
       ids <- IdentSet.union ids (fv_expr expr);
       DoChildren
  method! vexpr = function
    | Expr_TApply (f, tes, args) ->
       if is_getter f then begin
         ids <- IdentSet.union ids (unionSets (List.map fv_expr args));
       end;
       begin match instantiate_fun_ret_typ f tes with
         | Some (Type_Bits e) -> ids <- IdentSet.union ids (fv_expr e)
         | _ -> ()
       end;
       DoChildren
    | _ -> DoChildren
  method! vlexpr = function
    | LExpr_Write (_, _, args)
    | LExpr_ReadWrite (_, _, _, args) ->
       ids <- IdentSet.union ids (unionSets (List.map fv_expr args));
       DoChildren
    | _ -> DoChildren
end

let slice_vars_of_stmts stmts =
  let open LibASL.Asl_visitor in
  let svs = new sliceVarsClass in
  ignore (visit_stmts (svs :> aslVisitor) stmts);
  svs#result

(* We add type variables of functions that appear only in the return type
   as implicit arguments of the translated function in Sail. *)
let ft_implicits ((_, _, tvs, _, atys, rty) : ASL_TC.funtype) =
  let arg_ids = IdentSet.of_list (List.map (fun (_, id) -> id) atys) in
  IdentSet.diff (fv_type rty) (IdentSet.union (fv_args atys) arg_ids)

let get_fun_implicits (id : ASL_AST.ident) : ASL_AST.ident list =
  match get_asl_funtype id with
  | Some ((_, _, tvs, _, _, _) as ft)
    when not (StringSet.mem (name_of_ident id) builtins) ->
     List.filter (fun id -> ASL_Utils.IdentSet.mem id (ft_implicits ft)) tvs
  | _ -> []

let instantiate_fun_implicits (id : ASL_AST.ident) (tes : ASL_AST.expr list) =
  match get_asl_funtype id with
  | Some ((_, _, tvs, _, _, _) as ft)
    when List.length tvs = List.length tes
         && not (StringSet.mem (name_of_ident id) builtins) ->
     let implicit_arg tv e = if IdentSet.mem tv (ft_implicits ft) then [e] else [] in
     List.concat (List.map2 implicit_arg tvs tes)
  | _ -> []

(* Collect variables that are assigned to like in the visitor class defined
   in ASL_Utils, but additionally take into account mutable arguments of
   setter functions. *)
class assignedVarsClass = object
  inherit ASL_Utils.assignedVarsClass

  method! vlexpr = function
    | LExpr_ReadWrite (setter, _, _, args)
    | LExpr_Write (setter, _, args) ->
       begin match get_asl_sfuntype setter with
         | Some (_, _, _, formals, _) ->
            let assigned = function
              | (Formal_InOut _, expr) -> fv_expr expr
              | (Formal_In _, _) -> IdentSet.empty
            in
            avs <- unionSets (avs :: List.map assigned (List.combine formals args));
            DoChildren
         | None -> DoChildren
       end
    | _ -> DoChildren
end

let assigned_vars_of_stmts stmts =
  let open LibASL.Asl_visitor in
  let avs = new assignedVarsClass in
  ignore (visit_stmts (avs :> aslVisitor) stmts);
  avs#result

let assigned_vars_of_decl decl =
  let open LibASL.Asl_visitor in
  let avs = new assignedVarsClass in
  ignore (visit_decl (avs :> aslVisitor) decl);
  avs#result

let rec has_setter_lexpr = function
  | LExpr_Wildcard | LExpr_Var _ -> false
  | LExpr_Array (le, _) | LExpr_Slices (le, _)
  | LExpr_Field (le, _) | LExpr_Fields (le, _) ->
     has_setter_lexpr le
  | LExpr_BitTuple les | LExpr_Tuple les ->
     List.exists has_setter_lexpr les
  | LExpr_Write _ | LExpr_ReadWrite _ -> true

let pp_to_string doc =
  let b = Buffer.create 120 in
  PPrint.ToBuffer.pretty 1. 120 b doc;
  Buffer.contents b

let remove_underscores str = String.concat "" (String.split_on_char '_' str)
let remove_spaces str = String.concat "" (String.split_on_char ' ' str)

let int_of_intLit (i : ASL_AST.intLit) = Big_int.of_string i
let int_of_hexLit (i : ASL_AST.hexLit) =
  Big_int.of_string ("0x" ^ (remove_underscores i))
let width_of_hexLit (i : ASL_AST.hexLit) =
  4 * String.length (remove_underscores i)

let unit_ty = ASL_TC.type_unit

let ids_of_binop bo =
  let open ASL_TC in
  GlobalEnv.getOperators2 env0 ASL_AST.Unknown bo
  |> List.map ft_id |> ASL_Utils.IdentSet.of_list

let is_keyword =
  let val_rexpr = Str.regexp_string "val" in
  let vector_rexpr = Str.regexp_string "vector" in
  let option_rexpr = Str.regexp_string "option" in
  let inc_rexpr = Str.regexp_string "inc" in
  function s ->
    Str.string_match val_rexpr s 0 ||
    Str.string_match vector_rexpr s 0 ||
    Str.string_match option_rexpr s 0 ||
    Str.string_match inc_rexpr s 0

let str_replace s with_ in_ = Str.global_replace (Str.regexp s) with_ in_
let str_remove s in_ = Str.global_replace (Str.regexp s) "" in_

let mk_op_id str = Id_aux (Operator str, Parse_ast.Unknown)

let mangle_name s =
  let remove_slash = str_replace "/" "_" s in
  let remove_dash = str_remove "-" remove_slash in
  let remove_lt = str_replace "<" "_" remove_dash in
  let remove_gt = str_replace ">" "_" remove_lt in
  let remove_colon = str_replace ":" "_" remove_gt in
  let remove_dot = str_replace "\\." "_" remove_colon in
  remove_dot

let sailify_name s =
  let str =
    match s with
    (* | "++"  -> "concat_str" *)
    | "MOD" -> "%"
    | "DIV" -> "/"
    | "REM" -> "%" (* Check this *)
    | "/"   -> "/"
    | "EOR" -> "^"
    | "OR"  -> "|"
    | "||"  -> "|"
    | "AND" -> "&"
    | "&&"  -> "&"
    | "<<"  -> "shl_int"
    | ">>"  -> "shr_int"
    | "shift_left_int" -> "shl_int"
    (* | "__consistent" -> "==" *) (* ? *)
    | "<" | "<=" | ">" | ">=" -> s (* Make sure to preserve the functions that can have < and > in their names *)
    | "!" -> "~"  (* bit negation *)
    | "-" -> "-" (* int negation *)
    | "NOT" -> "~"
    | "Len" -> "length"
    | "print" -> "print"
    | "type" -> "typ"
    | "Int" -> "asl_Int"
    | "match" -> "val_match"
    | "unsigned" -> "is_unsigned"
    | "signed" -> "is_signed"
    | "add_int" -> "add_atom"
    | "sub_int" -> "sub_atom"
    | "le_int" -> "lteq_int"
    | "ge_int" -> "gteq_int"
    | "neg_int" -> "negate"
    | "append_bits" -> "append"
    | "and_bits" -> "and_vec"
    | "not_bits" -> "not_vec"
    | "or_bits" -> "or_vec"
    | "ne_int" -> "neq_int"
    | "ne_bool" -> "neq_bool"
    | "ne_bits" -> "neq_bits"
    | "ne_real" -> "neq_real"
    | "Sqrt" -> "sqrt"
    | _ ->
      (*if is_decode s
      then fix_decode_name (str_remove "aarch64_instrs_" (str_replace "__decode" "_decode" remove_dot))
      else if is_execute s
      then str_remove "aarch64_instrs_" (str_remove "_execute" remove_dot)
      else*) if is_keyword s
      then s ^ "_name"
      else mangle_name s
  in
  mk_id str

let sailify_binop (op : ASL_AST.binop) =
  match op with
  | ASL_AST.Binop_Eq -> mk_op_id "=="
  | ASL_AST.Binop_NtEq -> mk_op_id "!="
  | ASL_AST.Binop_Gt -> mk_op_id ">"
  | ASL_AST.Binop_GtEq -> mk_op_id ">="
  | ASL_AST.Binop_Lt -> mk_op_id "<"
  | ASL_AST.Binop_LtEq -> mk_op_id "<="
  | ASL_AST.Binop_Plus -> mk_op_id "+"
  | ASL_AST.Binop_Minus -> mk_op_id "-"
  | ASL_AST.Binop_Multiply -> mk_op_id "*"
  | ASL_AST.Binop_Divide -> mk_op_id "/"
  | ASL_AST.Binop_Power -> mk_op_id "^"
  | ASL_AST.Binop_Quot -> mk_id "QUOT"
  | ASL_AST.Binop_Rem -> mk_id "REM"
  | ASL_AST.Binop_Div -> mk_id "DIV"
  | ASL_AST.Binop_Mod -> mk_id "MOD"
  | ASL_AST.Binop_ShiftL -> mk_op_id "<<"
  | ASL_AST.Binop_ShiftR -> mk_op_id ">>"
  | ASL_AST.Binop_BoolAnd -> mk_op_id "&"
  | ASL_AST.Binop_BoolOr -> mk_op_id "|"
  | ASL_AST.Binop_BoolIff -> mk_op_id "<->"
  | ASL_AST.Binop_BoolImplies -> mk_op_id "-->"
  | ASL_AST.Binop_BitOr -> mk_op_id "|"
  | ASL_AST.Binop_BitEor -> mk_id "EOR"
  | ASL_AST.Binop_BitAnd -> mk_op_id "&"
  | ASL_AST.Binop_Append -> mk_op_id "++"
  | ASL_AST.Binop_Concat -> mk_op_id "@"
  | ASL_AST.Binop_DUMMY -> mk_id "DUMMY"

let sailify_unop (op : ASL_AST.unop) =
  let str =
    match op with
    | ASL_AST.Unop_Negate -> "-"
    | ASL_AST.Unop_BoolNot -> "~"
    | ASL_AST.Unop_BitsNot -> "~"
  in
  mk_id str

let sailify_type_name s =
  match s with
  | "boolean" -> "bool"
  | "integer" -> "int"
  | "__RAM" -> "bits" (* TODO: unclear how to handle properly *)
  | _ -> mangle_name s

let suffix_of_ident = function
  | ASL_AST.Ident _ -> ""
  | ASL_AST.FIdent (name, idx) ->
     if idx = 0 then ""
     else if StringSet.mem name builtins then ""
     else ("__" ^ string_of_int idx)

let sail_id_of_ident (id : ASL_AST.ident) =
  append_id (sailify_name (name_of_ident id)) (suffix_of_ident id)

let sail_kid_of_ident id = kid_of_id (sail_id_of_ident id)

let sail_type_id_of_ident id =
  append_id (mk_id (sailify_type_name (name_of_ident id))) (suffix_of_ident id)

let bits_typ nexp =
  mk_typ (Typ_app (mk_id "bits", [mk_typ_arg (A_nexp nexp)]))

let is_bits_typ (Typ_aux (t_aux, _)) = match t_aux with
  | Typ_app (bits, _) -> string_of_id bits = "bits"
  | _ -> false

let is_enum ctx id =
  match Type_check.Env.lookup_id id ctx.tc_env with
  | Enum _ -> true
  | _ -> false

let kopts_of_vars ctx (vars : ASL_Utils.IdentSet.t) =
  let add_kid var kids =
    let kid = sail_kid_of_ident var in
    if KBindings.mem kid (Type_check.Env.get_typ_vars ctx.tc_env) then
      kids
    else
      KidSet.add kid kids
  in
  ASL_Utils.IdentSet.fold add_kid vars KidSet.empty
  |> KidSet.elements |> List.map (mk_kopt K_int)

let kopts_of_funtype ctx ret_ty args =
  ASL_Utils.fv_args args
  |> ASL_Utils.IdentSet.union (ASL_Utils.fv_type ret_ty)
  |> ASL_TC.removeConsts (ASL_TC.env0)
  |> kopts_of_vars ctx

let construct_pexp (pat, guard) exp =
  match guard with
  | Some g -> mk_pexp (Pat_when (pat, g, exp))
  | None -> mk_pexp (Pat_exp (pat, exp))

let combine_guards op g1 g2 =
  match (g1, g2) with
  | (Some g1, Some g2) -> Some (mk_exp (E_app_infix (g1, mk_id op, g2)))
  | (Some g1, None) -> Some g1
  | (None, Some g2) -> Some g2
  | (None, None) -> None

let int_var_typ id = atom_typ (nvar (kid_of_id id))

let int_var_pat id =
  let tpat = mk_typ_pat (TP_var (kid_of_id id)) in
  mk_pat (P_var (mk_pat (P_id id), tpat))

let check_local (test : lvar -> bool) ctx id =
  try test (Bindings.find id ctx.locals) with
  | Not_found -> false
let is_owned_local = check_local lvar_is_owned
let is_shared_local = check_local lvar_is_shared
let is_mutable_local = check_local lvar_is_mutable
let is_number_local = check_local (fun lvar -> is_number (lvar_typ lvar))
let is_bits_local = check_local (fun lvar -> is_bits_typ (lvar_typ lvar))

let local_typ ctx id = lvar_typ (Bindings.find id ctx.locals)

let declare_local ?mut:(mut=Mutable) id typ ctx =
  { ctx with locals = Bindings.add id (Owned (mut, typ)) ctx.locals }

let declare_immutable = declare_local ~mut:Immutable

let redeclare_immutable id ctx =
  declare_immutable id (local_typ ctx id) ctx

let share_locals ids ctx =
  let share id lvar = if IdentSet.mem id ids then share_lvar lvar else lvar in
  { ctx with locals = Bindings.mapi share ctx.locals }

let constrained_vars_of_stmts ctx stmts =
  let slice_vars = slice_vars_of_stmts stmts in
  let assigns_stmt = assigned_vars_of_stmts stmts in
  IdentSet.diff slice_vars assigns_stmt
  |> IdentSet.filter (is_mutable_local ctx)
  |> IdentSet.filter (is_number_local ctx)

let needs_rebind ctx stmt =
  not (IdentSet.is_empty (constrained_vars_of_stmts ctx [stmt]))

let fails f arg =
  match f arg with
  | _ -> false
  | exception _ -> true

let succeeds f arg = not (fails f arg)

let rec stmt_final = function
  | Stmt_FunReturn _ | Stmt_ProcReturn _
  | Stmt_Undefined _ | Stmt_Dep_Undefined _
  | Stmt_Unpred _ | Stmt_Dep_Unpred _
  | Stmt_ImpDef _| Stmt_Dep_ImpDef _
  | Stmt_ExceptionTaken _ | Stmt_See _
  | Stmt_ConstrainedUnpred _ | Stmt_Throw _ -> true
  | Stmt_TCall (f, _, _, _) ->
     name_of_ident f = "EndOfInstruction"
     || name_of_ident f = "Unreachable"
  | Stmt_Case (_, alts, otherwise, _) ->
     let alt_final (Alt_Alt (_, _, stmts)) = stmts_final stmts in
     List.for_all alt_final alts
     && (match otherwise with Some stmts -> stmts_final stmts | None -> true)
  | _ -> false

and stmts_final stmts = List.exists stmt_final stmts

let stmts_not_final stmts = not (stmts_final stmts)

let rec initialised_vars = function
  | ((Stmt_VarDecl _ | Stmt_Assign _) as stmt) :: rest ->
     let assigned = assigned_vars_of_stmts [stmt] in
     let used = fv_stmts [stmt] in
     IdentSet.diff (IdentSet.union assigned (initialised_vars rest)) used
  | Stmt_If (cond, tstmts, elsifs, estmts, _) :: rest ->
     let elsif_stmts (S_Elsif_Cond (_, eistmts)) = eistmts in
     let blocks =
       tstmts :: estmts :: List.map elsif_stmts elsifs
       |> List.filter stmts_not_final
     in
     let iv_blocks = match List.map initialised_vars blocks with
       | [] -> IdentSet.empty
       | i :: is -> List.fold_left IdentSet.inter i is
     in
     IdentSet.diff (IdentSet.union iv_blocks (initialised_vars rest)) (fv_expr cond)
  | Stmt_Case (e, alts, fallthrough, _) :: rest ->
     let alt_stmts (Alt_Alt (_, _, astmts)) = astmts in
     let ft_stmts = match fallthrough with
       | Some stmts -> [stmts]
       | None -> []
     in
     let clauses =
       ft_stmts @ List.map alt_stmts alts
       |> List.filter stmts_not_final
     in
     let iv_clauses = match List.map initialised_vars clauses with
       | [] -> IdentSet.empty
       | c :: cs -> List.fold_left IdentSet.inter c cs
     in
     IdentSet.diff (IdentSet.union iv_clauses (initialised_vars rest)) (fv_expr e)
  | stmt :: rest -> IdentSet.diff (initialised_vars rest) (fv_stmts [stmt])
  | [] -> IdentSet.empty

let rec initial_assignment id = function
  | Stmt_Assign (LExpr_Var id', e, _) :: _
    when Id.compare id id' = 0 && not (IdentSet.mem id (fv_expr e)) ->
     Some e
  | stmt :: stmts ->
     let used = fv_stmts [stmt] in
     let assigned = assigned_vars_of_stmts [stmt] in
     if IdentSet.mem id (IdentSet.union used assigned) then None else
     initial_assignment id stmts
  | [] -> None

module BigInt = struct
  type t = Big_int.num
  let compare = Big_int.compare
end

module BigIntSet = Set.Make(BigInt)

type int_constraint =
  | IC_Set of BigIntSet.t
  | IC_Range of BigInt.t * BigInt.t
  | IC_Unknown

let merge_int_constraint ic1 ic2 =
  match (ic1, ic2) with
  | (IC_Set s1, IC_Set s2) -> IC_Set (BigIntSet.union s1 s2)
  | (IC_Range (l1, h1), IC_Range (l2, h2)) ->
     IC_Range (Big_int.min l1 l2, Big_int.max h1 h2)
  | (IC_Set set, IC_Range (lo, hi))
  | (IC_Range (lo, hi), IC_Set set) ->
     let lo' = Big_int.min lo (BigIntSet.min_elt set) in
     let hi' = Big_int.max hi (BigIntSet.max_elt set) in
     IC_Range (lo', hi')
  | _ -> IC_Unknown

let merge_int_constraints (ics1 : int_constraint Bindings.t) (ics2 : int_constraint Bindings.t) =
  let merge _ ic1 ic2 = Some (merge_int_constraint ic1 ic2) in
  Bindings.union merge ics1 ics2

let is_small_range lo hi =
  let size = Big_int.succ (Big_int.sub hi lo) in
  Big_int.less_equal size (Big_int.of_int 8)

let set_of_small_range lo hi =
  let size = Big_int.to_int (Big_int.succ (Big_int.sub hi lo)) in
  if size <= 8 then
    let element idx = Big_int.add lo (Big_int.of_int idx) in
    BigIntSet.of_list (List.init size element)
  else failwith ("set_of_small_range: range too big")

let map_int_constraint f = function
  | IC_Set is -> IC_Set (BigIntSet.map f is)
  | IC_Range (lo, hi) when is_small_range lo hi ->
     IC_Set (BigIntSet.map f (set_of_small_range lo hi))
  | IC_Range (lo, hi) ->
     let lo' = f lo in
     let hi' = f hi in
     IC_Range (Big_int.min lo' hi', Big_int.max lo' hi')
  | IC_Unknown -> IC_Unknown

let rec int_constraint_of_expr known_vars = function
  | Expr_LitInt i -> IC_Set (BigIntSet.singleton (int_of_intLit i))
  | Expr_If (_, texpr, [], eexpr) ->
     let ic1 = int_constraint_of_expr known_vars texpr in
     let ic2 = int_constraint_of_expr known_vars eexpr in
     merge_int_constraint ic1 ic2
  | Expr_Var id when Bindings.mem id known_vars ->
     Bindings.find id known_vars
  | Expr_TApply (uint, [nbits], _)
    when name_of_ident uint = "UInt" ->
     begin match int_constraint_of_expr known_vars nbits with
       | IC_Set is when BigIntSet.cardinal is = 1 ->
          let i' = Big_int.to_int (BigIntSet.choose is) in
          IC_Range (Big_int.zero, Big_int.pred (Big_int.pow_int (Big_int.of_int 2) i'))
       | _ -> IC_Unknown
     end
  | Expr_TApply (highestsetbit, [nbits], _)
    when name_of_ident highestsetbit = "HighestSetBit" ->
     begin match int_constraint_of_expr known_vars nbits with
       | IC_Set is when BigIntSet.cardinal is = 1 ->
          IC_Range (Big_int.of_int (-1), Big_int.pred (BigIntSet.choose is))
       | _ -> IC_Unknown
     end
  | Expr_TApply (lowestsetbit, [nbits], _)
    when name_of_ident lowestsetbit = "LowestSetBit" ->
     begin match int_constraint_of_expr known_vars nbits with
       | IC_Set is when BigIntSet.cardinal is = 1 ->
          IC_Range (Big_int.of_int 0, BigIntSet.choose is)
       | _ -> IC_Unknown
     end
  | Expr_TApply (add_int, _, [Expr_LitInt i; operand])
  | Expr_TApply (add_int, _, [operand; Expr_LitInt i])
    when name_of_ident add_int = "add_int" ->
     let add_i j = Big_int.add j (int_of_intLit i) in
     map_int_constraint add_i (int_constraint_of_expr known_vars operand)
  | Expr_TApply (sub_int, _, [Expr_LitInt i; operand])
    when name_of_ident sub_int = "sub_int" ->
     let i_sub j = Big_int.sub (int_of_intLit i) j in
     map_int_constraint i_sub (int_constraint_of_expr known_vars operand)
  | Expr_TApply (sub_int, _, [operand; Expr_LitInt i])
    when name_of_ident sub_int = "sub_int" ->
     let sub_i j = Big_int.sub j (int_of_intLit i) in
     map_int_constraint sub_i (int_constraint_of_expr known_vars operand)
  | Expr_TApply (mul_int, _, [Expr_LitInt i; operand])
  | Expr_TApply (mul_int, _, [operand; Expr_LitInt i])
    when name_of_ident mul_int = "mul_int" ->
     let mul_i j = Big_int.mul j (int_of_intLit i) in
     map_int_constraint mul_i (int_constraint_of_expr known_vars operand)
  | Expr_TApply (fdiv_int, _, [operand; Expr_LitInt i])
    when name_of_ident fdiv_int = "fdiv_int" ->
     let i' = int_of_intLit i in
     let is_multiple j =
       Big_int.greater j Big_int.zero
       && Big_int.greater i' Big_int.zero
       && Big_int.equal (Big_int.modulus j i') Big_int.zero
     in
     let div_i j = Big_int.div j i' in
     begin match int_constraint_of_expr known_vars operand with
       | IC_Set is when BigIntSet.for_all is_multiple is ->
          IC_Set (BigIntSet.map div_i is)
       | _ -> IC_Unknown
     end
  (* Particular small left-shifts are common in decoders and are special-cased
     in the Sail prelude. *)
  | Expr_TApply (shl_int, _, [Expr_LitInt i; arg])
    when name_of_ident shl_int = "shift_left_int" ->
     let i = Big_int.of_string i in
     let shift amount =
       let amount = Big_int.to_int amount in
       if amount < 0 then Big_int.shift_right i (abs amount) else
       Big_int.shift_left i amount
     in
     begin match int_constraint_of_expr known_vars arg with
       | IC_Set is when BigIntSet.cardinal is > 1 ->
          IC_Set (BigIntSet.map shift is)
       | IC_Range (lo, hi) when is_small_range lo hi ->
          IC_Set (BigIntSet.map shift (set_of_small_range lo hi))
       (* | IC_Range (lo, hi)
         when Big_int.less_equal (Big_int.succ (Big_int.sub hi lo)) (Big_int.of_int 8) ->
          let len = Big_int.to_int (Big_int.succ (Big_int.sub hi lo)) in
          let lo = Big_int.to_int lo in
          let shift idx =
            let amount = lo + idx in
            if amount < 0 then Big_int.shift_right i (abs amount) else
            Big_int.shift_left i amount
          in
          IC_Set (BigIntSet.of_list (List.init len shift)) *)
       | _ -> IC_Unknown
     end
  | Expr_Parens expr -> int_constraint_of_expr known_vars expr
  | _ -> IC_Unknown

class intConstraintsClass known_vars = object(self)
  inherit LibASL.Asl_visitor.nopAslVisitor

  val mutable constraints = (Bindings.empty : int_constraint Bindings.t)
  method result = constraints
  method add_constraint id c =
    let c' = match Bindings.find id constraints with
      | c' -> merge_int_constraint c c'
      | exception Not_found -> c
    in
    constraints <- Bindings.add id c' constraints
  method! vstmt = function
    | Stmt_Assign (LExpr_Var id, expr, _)
    | Stmt_VarDecl (_, id, expr, _)
    | Stmt_ConstDecl (_, id, expr, _) ->
       self#add_constraint id (int_constraint_of_expr known_vars expr);
       SkipChildren
    | (Stmt_Assign _ as stmt) ->
       let ids = assigned_vars_of_stmts [stmt] in
       IdentSet.iter (fun id -> self#add_constraint id IC_Unknown) ids;
       SkipChildren
    | _ -> DoChildren
end

let int_constraints_of_stmts ?known_vars:(kv=Bindings.empty) stmts =
  let open LibASL.Asl_visitor in
  let icc = new intConstraintsClass kv in
  ignore (visit_stmts (icc :> aslVisitor) stmts);
  icc#result

let nc_of_int_constraint var constr =
  let kid = sail_kid_of_ident var in
  match constr with
  | IC_Set is ->
     begin match BigIntSet.elements is with
       | [i] -> Some (nc_eq (nvar kid) (nconstant i))
       | is -> Some (nc_set kid is)
     end
  | IC_Range (lo, hi) when Big_int.less_equal Big_int.zero lo ->
     let n = Big_int.succ (Big_int.sub hi lo) in
     if Big_int.less_equal n (Big_int.of_int 8) then begin
         (* Enumerate small intervals as sets, which are more easily
            picked up by the Sail monomorphisation analysis. *)
         let element i = Big_int.add lo (Big_int.of_int i) in
         Some (nc_set kid (List.init (Big_int.to_int n) element))
       end else begin
         let lo' = nc_lteq (nconstant lo) (nvar kid) in
         let hi' = nc_lteq (nvar kid) (nconstant hi) in
         Some (nc_and lo' hi')
       end
  | _ -> None

let sail_typ_of_int_constraint var constr =
  match constr with
  | IC_Set is when not (BigIntSet.is_empty is) ->
     let kid = sail_kid_of_ident var in
     begin match nc_of_int_constraint var constr with
       | Some nc ->
          mk_typ (Typ_exist ([mk_kopt K_int kid], nc, atom_typ (nvar kid)))
       | None -> int_typ
     end
  | IC_Range (lo, hi) when Big_int.less_equal Big_int.zero lo ->
     range_typ (nconstant lo) (nconstant hi)
  | _ -> int_typ

let initial_expr_of_int_constraint = function
  | IC_Set is when not (BigIntSet.is_empty is) ->
     Some (Expr_LitInt (Big_int.to_string (BigIntSet.choose is)))
  | _ -> None

let initial_exp_of_int_constraint = function
  | IC_Set is when not (BigIntSet.is_empty is) ->
     mk_lit_exp (L_num (BigIntSet.choose is))
  (* | IC_Range (lo, hi) when Big_int.less_equal Big_int.zero lo ->
     mk_lit_exp (L_num lo) *)
  | _ -> mk_lit_exp L_undef

let sail_intLits_type ints =
  let ints' = StringSet.of_list ints |> StringSet.elements |> List.map Big_int.of_string in
  Type_check.exist_typ (fun kid -> nc_set kid ints') (fun kid -> atom_typ (nvar kid))

let rec expr_of_pattern (pat : pattern) =
  match pat with
  | Pat_LitInt i -> Expr_LitInt i
  | Pat_LitHex h -> Expr_LitHex h
  | Pat_LitBits b -> Expr_LitBits b
  | Pat_Const c -> Expr_Var c
  | Pat_Tuple ps -> Expr_Tuple (List.map expr_of_pattern ps)
  | Pat_Single e -> e
  | Pat_LitMask _ | Pat_Wildcard | Pat_Set _ | Pat_Range (_, _) ->
     failwith ("expr_of_pattern: " ^ pp_to_string (ASL_PP.pp_pattern pat))

let is_expr_pattern = succeeds expr_of_pattern

let rec pattern_of_expr (expr : expr) =
  match expr with
  | Expr_LitInt i -> Pat_LitInt i
  | Expr_LitHex h -> Pat_LitHex h
  | Expr_LitBits b -> Pat_LitBits b
  | Expr_Var v -> Pat_Const v
  | Expr_Tuple es -> Pat_Tuple (List.map pattern_of_expr es)
  | _ ->
     failwith ("pattern_of_expr: " ^ pp_to_string (ASL_PP.pp_expr expr))

let is_pattern_expr = succeeds pattern_of_expr

let rec lexpr_of_expr (expr : expr) =
  match expr with
  | Expr_Var id -> LExpr_Var id
  | Expr_Slices (e, slices) -> LExpr_Slices (lexpr_of_expr e, slices)
  | Expr_Field (e, field) -> LExpr_Field (lexpr_of_expr e, field)
  | Expr_Fields (e, fields) -> LExpr_Fields (lexpr_of_expr e, fields)
  | Expr_Array (e, idx) -> LExpr_Array (lexpr_of_expr e, idx)
  | Expr_Tuple es -> LExpr_Tuple (List.map lexpr_of_expr es)
  | Expr_TApply (getter, targs, args) when is_getter getter ->
     let regexp = Str.regexp_string ".read" in
     let setter = match args with
       | [] -> Str.global_replace regexp ".write" (name_of_ident getter)
       | (_::_) -> Str.global_replace regexp ".set" (name_of_ident getter)
     in
     LExpr_Write (Ident (setter), targs, args)
  | _ ->
     failwith ("lexpr_of_expr: " ^ pp_to_string (ASL_PP.pp_expr expr))

let rec int_of_expr (expr : ASL_AST.expr) =
  match expr with
  | Expr_LitInt i | Expr_LitHex i ->
     Some (Big_int.of_string i)
  | Expr_Binop (e1, Binop_Plus, e2) ->
     (match (int_of_expr e1, int_of_expr e2) with
      | (Some i1, Some i2) -> Some (Big_int.add i1 i2)
      | _ -> None)
  | Expr_Binop (e1, Binop_Minus, e2) ->
     (match (int_of_expr e1, int_of_expr e2) with
      | (Some i1, Some i2) -> Some (Big_int.sub i1 i2)
      | _ -> None)
  | Expr_Parens e -> int_of_expr e
  | _ -> None

let expr_is_intlit expr = (int_of_expr expr <> None)

let width_of_slice (slice : ASL_AST.slice) =
  match slice with
  | ASL_AST.Slice_Single e -> Expr_LitInt "1"
  | ASL_AST.Slice_HiLo (hi, lo) ->
     Expr_Binop (Expr_Binop (hi, Binop_Minus, lo), Binop_Plus, Expr_LitInt "1")
  | ASL_AST.Slice_LoWd (lo, wd) -> wd

let slice_low_idx = function
  | Slice_Single lo
  | Slice_LoWd (lo, _)
  | Slice_HiLo (_, lo) -> lo

let is_slice_lowd = function
  | Slice_LoWd _ -> true
  | _ -> false

let const_width_slice (slice : ASL_AST.slice) =
  expr_is_intlit (width_of_slice slice)

let int_of_slice_width (slice : ASL_AST.slice) =
  match int_of_expr (width_of_slice slice) with
  | Some i -> i
  | None -> failwith ("int_of_slice_width: " ^ pp_to_string (ASL_PP.pp_slice slice))

let measure_none = Measure_aux (Measure_none, Parse_ast.Unknown)

let rec add_final_return_stmt ty stmts =
  let ret = Stmt_FunReturn (Expr_Unknown ty, Unknown) in
  match List.rev stmts with
  | Stmt_FunReturn (_, _) :: _
  | (Stmt_Throw _ | Stmt_Unpred _ | Stmt_See _ | Stmt_ExceptionTaken _) :: _
  | (Stmt_ImpDef _ | Stmt_Undefined _ | Stmt_Dep_ImpDef _) :: _ ->
     stmts
  | Stmt_If (c, t, es, e, l) :: rstmts ->
     let t' = add_final_return_stmt ty t in
     let es' = List.map (add_final_return_elsif ty) es in
     let e' = add_final_return_stmt ty e in
     List.rev (Stmt_If (c, t', es', e', l) :: rstmts)
  | Stmt_Case (e, alts, otherwise, l) :: rstmts ->
     let alts' = List.map (add_final_return_alt ty) alts in
     let otherwise' = add_final_return_optstmts ty otherwise in
     List.rev (Stmt_Case (e, alts', otherwise', l) :: rstmts)
  | Stmt_Try (stmts, ex, catchers, otherwise, l) :: rstmts ->
     let stmts' = add_final_return_stmt ty stmts in
     let catchers' = List.map (add_final_return_catcher ty) catchers in
     let otherwise' = add_final_return_optstmts ty otherwise in
     List.rev (Stmt_Try (stmts', ex, catchers', otherwise', l) :: rstmts)
  | rstmts -> List.rev (ret :: rstmts)

and add_final_return_elsif ty (S_Elsif_Cond (e, stmts)) =
  S_Elsif_Cond (e, add_final_return_stmt ty stmts)

and add_final_return_alt ty (Alt_Alt (pat, guard, stmts)) =
  Alt_Alt (pat, guard, add_final_return_stmt ty stmts)

and add_final_return_catcher ty (Catcher_Guarded (e, stmts)) =
  Catcher_Guarded (e, add_final_return_stmt ty stmts)

and add_final_return_optstmts ty = function
  | Some stmts -> Some (add_final_return_stmt ty stmts)
  | None -> Some (add_final_return_stmt ty [])

let args_of_exps args =
  if args = [] then [mk_lit_exp L_unit] else args

let rec sail_of_expr ctx (expr : ASL_AST.expr) =
  let recur = sail_of_expr ctx in
  match expr with
  | Expr_TApply _ when ExprMap.mem expr ctx.bound_exprs ->
     mk_exp (E_id (sail_id_of_ident (ExprMap.find expr ctx.bound_exprs)))
  | ASL_AST.Expr_If (c, t, eifs, e) ->
     let else_exp =
       match eifs with
       | ASL_AST.E_Elsif_Cond (c', t') :: eifs ->
          recur (ASL_AST.Expr_If (c', t', eifs, e))
       | [] -> recur e
     in
     mk_exp (E_if (recur c, recur t, else_exp))
  | ASL_AST.Expr_Binop (Expr_LitInt "2", Binop_Power, e) ->
     mk_exp (E_app (mk_id "pow2", [recur e]))
  | ASL_AST.Expr_Binop (e1, op, e2) ->
     begin match sailify_binop op with
     | Id_aux (Operator "@", _) ->
        mk_exp (E_vector_append (recur e1, recur e2))
     | Id_aux (Operator op', l) ->
        mk_exp (E_app_infix (recur e1, Id_aux (Id op', l), recur e2))
     | Id_aux (Id _, _) as id' ->
        mk_exp (E_app (id', [recur e1; recur e2]))
     end
  | ASL_AST.Expr_Field (e, f)
  | ASL_AST.Expr_Fields (e, [f]) ->
     mk_exp (E_field (recur e, sail_id_of_ident f))
  | ASL_AST.Expr_Fields (e, f :: fs) ->
     let f' = recur (Expr_Field (e, f)) in
     let fs' = recur (Expr_Fields (e, fs)) in
     mk_exp (E_vector_append (f', fs'))
  | ASL_AST.Expr_Fields (e, []) ->
     failwith ("sail_of_expr: Empty Expr_Fields")
  | ASL_AST.Expr_Slices (Expr_LitHex h, [slice])
    when slice_low_idx slice = Expr_LitInt "0" && const_width_slice slice ->
     let h' = mk_lit_exp (L_hex h) in
     let width = Big_int.of_int (width_of_hexLit h) in
     let width' = int_of_slice_width slice in
     if Big_int.equal width' width then h' else
     if Big_int.less width' width then
       mk_exp (E_app (mk_id "truncate", [h'; mk_lit_exp (L_num width')]))
     else
       mk_exp (E_app (mk_id "ZeroExtend", [h'; mk_lit_exp (L_num width')]))
  | ASL_AST.Expr_Slices (e, [Slice_Single idx]) ->
     mk_exp (E_vector [mk_exp (E_vector_access (recur e, recur idx))])
  | ASL_AST.Expr_Slices (e, [slice]) ->
     sail_slice_exp ctx slice (recur e)
  | ASL_AST.Expr_Slices (e, slice :: slices) ->
     let slices' = recur (ASL_AST.Expr_Slices (e, slices)) in
     mk_exp (E_vector_append (sail_slice_exp ctx slice (recur e), slices'))
  | ASL_AST.Expr_Var id when pprint_ident id = "TRUE" -> mk_lit_exp L_true
  | ASL_AST.Expr_Var id when pprint_ident id = "FALSE" -> mk_lit_exp L_false
  | ASL_AST.Expr_Var id ->
     let is_ty_var =
       let tvars =
         unionSets (List.map fv_type (List.map fst ctx.fun_args))
         |> IdentSet.filter (fun id -> ASL_TC.GlobalEnv.getConstant ASL_TC.env0 id = None)
       in
       let args = IdentSet.of_list (List.map snd ctx.fun_args) in
       IdentSet.mem id (IdentSet.diff tvars args)
     in
     if is_ty_var then mk_exp (E_sizeof (nvar (sail_kid_of_ident id))) else
     mk_exp (E_id (sail_id_of_ident id))
  | ASL_AST.Expr_Parens e ->
     recur e
  | ASL_AST.Expr_Unknown ty ->
     mk_exp (E_cast (sail_of_ty ctx ty, mk_lit_exp L_undef))
  | ASL_AST.Expr_ImpDef (ASL_AST.Type_Constructor tid, s) ->
     let s' = mk_lit_exp (L_string (Util.option_default "" s)) in
     let f = prepend_id "__IMPDEF_" (sail_id_of_ident tid) in
     mk_exp (E_app (f, [s']))
  | ASL_AST.Expr_ImpDef (ASL_AST.Type_Bits n, s) ->
     let s' = mk_lit_exp (L_string (Util.option_default "" s)) in
     mk_exp (E_app (mk_id "__IMPDEF_bits", [recur n; s']))
  (* | ASL_AST.Expr_TApply (f, _, [])
    when ASL_Utils.Bindings.mem f ctx.bound_tvars ->
     mk_exp (E_id (sail_id_of_ident (ASL_Utils.Bindings.find f ctx.bound_tvars))) *)
  | ASL_AST.Expr_TApply (op, _, [e1; e2])
    when ASL_Utils.Bindings.mem op !ASL_TC.binop_table ->
     recur (Expr_Binop (e1, ASL_Utils.Bindings.find op !ASL_TC.binop_table, e2))
  | ASL_AST.Expr_TApply (f, tes, args) ->
     let args' = List.map recur ((instantiate_fun_implicits f tes) @ args) in
     mk_exp (E_app (sail_id_of_ident f, args_of_exps args'))
  | ASL_AST.Expr_Array (e, idx) ->
     mk_exp (E_vector_access (recur e, recur idx))
  | ASL_AST.Expr_Tuple es ->
     mk_exp (E_tuple (List.map recur es))
  | ASL_AST.Expr_LitInt i -> mk_lit_exp (L_num (int_of_intLit i))
  | ASL_AST.Expr_LitHex h -> mk_exp (E_app (mk_id "UInt", [mk_lit_exp (L_hex h)]))
  | ASL_AST.Expr_LitReal r -> mk_lit_exp (L_real r)
  | ASL_AST.Expr_LitBits b -> mk_lit_exp (L_bin (remove_spaces b))
  | ASL_AST.Expr_LitString s -> mk_lit_exp (L_string s)
  | ASL_AST.Expr_In (e, ASL_AST.Pat_Set []) -> mk_lit_exp (L_false)
  | ASL_AST.Expr_In (e, ASL_AST.Pat_Set [ASL_AST.Pat_Range (r1, r2)]) ->
     let e' = sail_of_expr ctx e in
     let r1' = sail_of_expr ctx r1 in
     let r2' = sail_of_expr ctx r2 in
     mk_exp (E_app (mk_id "in_range", [e'; r1'; r2']))
  | ASL_AST.Expr_In (e, ASL_AST.Pat_Set (p :: ps))
    when List.for_all is_expr_pattern (p :: ps) ->
     let p' = mk_exp (E_app_infix (recur e, mk_id "==", recur (expr_of_pattern p))) in
     let rest = ASL_AST.Expr_In (e, ASL_AST.Pat_Set ps) in
     if ps = [] then p' else mk_exp (E_app_infix (p', mk_id "|", recur rest))
  (* TODO: Handle more special cases? Pat_LitMask could be handled using a match_mask helper function in Sail, for example, maybe even with infix syntax. *)
  | ASL_AST.Expr_In (e, pat) ->
     let pats =
       match pat with
       | ASL_AST.Pat_Set ps -> ps
       | _ -> [pat]
     in
     let clauses =
       List.map (fun p -> construct_pexp (sail_of_pat ctx p) (mk_lit_exp L_true)) pats @
       [mk_pexp (Pat_exp (mk_pat P_wild, mk_lit_exp L_false))]
     in
     mk_exp (E_cast (bool_typ, mk_exp (E_case (recur e, clauses))))
  | ASL_AST.Expr_Unop (_, _)
  | ASL_AST.Expr_Slices (_, _)
  | ASL_AST.Expr_ImpDef (_, _)
  | ASL_AST.Expr_LitMask _ ->
     failwith ("sail_of_expr: " ^ pp_to_string (ASL_PP.pp_expr expr))

and sail_slice_exps (ctx : ctx) (slice : ASL_AST.slice) =
  let (lowd, i1, i2) =
    match slice with
    | ASL_AST.Slice_Single i ->      (false, i, i)
    | ASL_AST.Slice_HiLo (hi, lo) -> (false, hi, lo)
    | ASL_AST.Slice_LoWd (lo, wd) -> (true, lo, wd)
  in
  let i1' = sail_of_expr ctx i1 in
  let i2' = sail_of_expr ctx i2 in
  let i12' =
    match (int_of_expr i1, int_of_expr i2) with
    | (Some int1, Some int2) ->
       mk_lit_exp (L_num (Big_int.pred (Big_int.add int1 int2)))
    | _ ->
       let sum = mk_exp (E_app_infix (i1', mk_id "+", i2')) in
       mk_exp (E_app_infix (sum, mk_id "-", mk_lit_exp (L_num (Big_int.of_int 1))))
  in
  if lowd then
    ((fun e -> mk_exp (E_app (mk_id "Slice", [e; i1'; i2']))),
    ((fun le -> mk_lexp (LEXP_vector_range (le, i12', i1'))),
     (fun e e' -> mk_exp (E_app (mk_id "SetSlice", [i2'; e; i1'; e'])))))
  else
    ((fun e -> mk_exp (E_vector_subrange (e, i1', i2'))),
    ((fun le -> mk_lexp (LEXP_vector_range (le, i1', i2'))),
     (fun e e' -> mk_exp (E_vector_update_subrange (e, i1', i2', e')))))
and sail_slice_exp ctx slice = fst (sail_slice_exps ctx slice)
and sail_slice_lexp ctx slice = fst (snd (sail_slice_exps ctx slice))
and sail_slice_update_exp ctx slice = snd (snd (sail_slice_exps ctx slice))

and sail_nexp_of_expr ctx (expr : ASL_AST.expr) =
  let recur = sail_nexp_of_expr ctx in
  match expr with
  | Expr_TApply _ when ExprMap.mem expr ctx.bound_exprs ->
     nvar (sail_kid_of_ident (ExprMap.find expr ctx.bound_exprs))
  | ASL_AST.Expr_LitInt i -> nconstant (int_of_intLit i)
  | ASL_AST.Expr_Var id ->
     let open ASL_TC in
     if GlobalEnv.getConstant env0 id = None then
       nvar (sail_kid_of_ident id)
     else
       nid (sail_id_of_ident id)
  | ASL_AST.Expr_Binop (e1, Binop_Multiply, e2) ->
     ntimes (recur e1) (recur e2)
  | ASL_AST.Expr_TApply (f, _, [e1; e2])
    when ASL_Utils.IdentSet.mem f (ids_of_binop Binop_Multiply) ->
     ntimes (recur e1) (recur e2)
  | ASL_AST.Expr_Binop (e1, Binop_Plus, ASL_AST.Expr_Unop (Unop_Negate, e2)) ->
     nminus (recur e1) (recur e2)
  | ASL_AST.Expr_Binop (e1, Binop_Plus, e2) ->
     nsum (recur e1) (recur e2)
  | ASL_AST.Expr_TApply (f, _, [e1; e2])
    when ASL_Utils.IdentSet.mem f (ids_of_binop Binop_Plus) ->
     nsum (recur e1) (recur e2)
  | ASL_AST.Expr_Binop (e1, Binop_Minus, e2) ->
     nminus (recur e1) (recur e2)
  | ASL_AST.Expr_TApply (f, _, [e1; e2])
    when ASL_Utils.IdentSet.mem f (ids_of_binop Binop_Minus) ->
     nminus (recur e1) (recur e2)
  | ASL_AST.Expr_Binop (e1, Binop_Div, e2) ->
     napp (mk_id "div") [recur e1; recur e2]
  | ASL_AST.Expr_TApply (f, _, [e1; e2])
    when ASL_Utils.IdentSet.mem f (ids_of_binop Binop_Div) ->
     napp (mk_id "div") [recur e1; recur e2]
  | ASL_AST.Expr_Parens e -> recur e
  | _ ->
     failwith ("sail_nexp_of_expr: " ^ pp_to_string (ASL_PP.pp_expr expr))

and sail_n_constraint_of_expr ctx (expr : ASL_AST.expr) =
  let recur = sail_n_constraint_of_expr ctx in
  let nexp_of = sail_nexp_of_expr ctx in
  match expr with
  | Expr_TApply (f, _, [e1; e2]) when IdentSet.mem f (ids_of_binop Binop_Eq) ->
     nc_eq (nexp_of e1) (nexp_of e2)
  | Expr_TApply (f, _, [e1; e2]) when IdentSet.mem f (ids_of_binop Binop_NtEq) ->
     nc_neq (nexp_of e1) (nexp_of e2)
  | Expr_TApply (f, _, [e1; e2]) when IdentSet.mem f (ids_of_binop Binop_GtEq) ->
     nc_gteq (nexp_of e1) (nexp_of e2)
  | Expr_TApply (f, _, [e1; e2]) when IdentSet.mem f (ids_of_binop Binop_Gt) ->
     nc_gt (nexp_of e1) (nexp_of e2)
  | Expr_TApply (f, _, [e1; e2]) when IdentSet.mem f (ids_of_binop Binop_LtEq) ->
     nc_lteq (nexp_of e1) (nexp_of e2)
  | Expr_TApply (f, _, [e1; e2]) when IdentSet.mem f (ids_of_binop Binop_Lt) ->
     nc_lt (nexp_of e1) (nexp_of e2)
  | Expr_TApply (f, _, [e1; e2]) when IdentSet.mem f (ids_of_binop Binop_BoolAnd) ->
     nc_and (recur e1) (recur e2)
  | Expr_TApply (f, _, [e1; e2]) when IdentSet.mem f (ids_of_binop Binop_BoolOr) ->
     nc_or (recur e1) (recur e2)
  | Expr_In (e, Pat_Set pats) when List.for_all is_expr_pattern pats ->
     let e' = nexp_of e in
     let clause pat = nc_eq e' (nexp_of (expr_of_pattern pat)) in
     List.fold_left nc_or nc_false (List.map clause pats)
  | Expr_Var id when name_of_ident id = "TRUE" -> nc_true
  | Expr_Var id when name_of_ident id = "FALSE" -> nc_false
  | _ ->
     failwith ("sail_n_constraint_of_expr: " ^ pp_to_string (ASL_PP.pp_expr expr))

and sail_of_lexpr ctx (lexpr : ASL_AST.lexpr) =
  let recur = sail_of_lexpr ctx in
  match lexpr with
  | ASL_AST.LExpr_Var v ->
     mk_lexp (LEXP_id (sail_id_of_ident v))
  | ASL_AST.LExpr_Slices (le, [slice]) ->
     sail_slice_lexp ctx slice (recur le)
  | ASL_AST.LExpr_Slices (le, ((_ :: _) as slices)) ->
     let le' = recur le in
     let slices' = List.map (fun s -> sail_slice_lexp ctx s le') slices in
     mk_lexp (LEXP_vector_concat slices')
  | ASL_AST.LExpr_Field (le, f) ->
     mk_lexp (LEXP_field (recur le, sail_id_of_ident f))
  | ASL_AST.LExpr_Fields (le, fs) ->
     let le' = recur le in
     let field f = mk_lexp (LEXP_field (le', sail_id_of_ident f)) in
     mk_lexp (LEXP_vector_concat (List.map field fs))
  | ASL_AST.LExpr_Tuple les ->
     mk_lexp (LEXP_tup (List.map recur les))
  | ASL_AST.LExpr_BitTuple les ->
     mk_lexp (LEXP_vector_concat (List.map recur les))
  | ASL_AST.LExpr_Array (le, e) ->
     mk_lexp (LEXP_vector (recur le, sail_of_expr ctx e))
  | ASL_AST.LExpr_Write (f, _, args) ->
     mk_lexp (LEXP_memory (sail_id_of_ident f, List.map (sail_of_expr ctx) args))
  | ASL_AST.LExpr_Wildcard ->
     mk_lexp (LEXP_id (fresh_id "__ignore"))
  | ASL_AST.LExpr_Slices (_, _)
  | ASL_AST.LExpr_ReadWrite (_, _, _, _) ->
     failwith ("sail_of_lexpr: " ^ pp_to_string (ASL_PP.pp_lexpr lexpr))

and sail_of_setter_assignment ctx f targs args rhs =
  let f' = sail_id_of_ident f in
  let implicits = instantiate_fun_implicits f targs in
  let args' = List.map (sail_of_expr ctx) (implicits @ args) in
  match get_asl_sfuntype f with
  | Some (_, _, _, formals, _) ->
     let formal_lexp = function
       | (Formal_InOut _, e) when succeeds lexpr_of_expr e ->
          [sail_of_lexpr ctx (lexpr_of_expr e)]
       | (Formal_InOut _, expr) ->
          failwith ("sail_of_setter_assignment: Unsupported InOut arg " ^ pp_expr expr)
       | (Formal_In _, _) -> []
     in
     begin match List.concat (List.map formal_lexp (List.combine formals args)) with
       | [] -> mk_exp (E_assign (mk_lexp (LEXP_memory (f', args')), rhs))
       | [lexp] -> mk_exp (E_assign (lexp, mk_exp (E_app (f', args' @ [rhs]))))
       | lexps ->
          let lexp = mk_lexp (LEXP_tup lexps) in
          mk_exp (E_assign (lexp, mk_exp (E_app (f', args' @ [rhs]))))
     end
  | _ ->
     mk_exp (E_assign (mk_lexp (LEXP_memory (f', args')), rhs))

and sail_of_tuple_assignment ctx lexps rhs =
  let pat_assignment idx = function
    | LExpr_Wildcard -> (mk_pat P_wild, [])
    | lexpr ->
       let id = "__tup_" ^ string_of_int idx in
       let id_pat = mk_pat (P_id (mk_id id)) in
       let pat = match infer_sail_lexpr_typ ctx lexpr with
         | Some typ -> mk_pat (P_typ (typ, id_pat))
         | None -> id_pat
       in
       (pat, [Stmt_Assign (lexpr, Expr_Var (Ident id), Unknown)])
  in
  let (pats, assignments) = List.split (List.mapi pat_assignment lexps) in
  let rhs' = sail_of_expr ctx rhs in
  let assignments' = sail_of_stmts ~force_block:true ctx (List.concat assignments) in
  mk_exp (E_let (mk_letbind (mk_pat (P_tup pats)) rhs', assignments'))

and sail_of_pat ctx (p : ASL_AST.pattern) =
  match p with
  | ASL_AST.Pat_LitInt i ->
     (mk_pat (P_lit (mk_lit (L_num (int_of_intLit i)))), None)
  | ASL_AST.Pat_LitHex h ->
     (mk_pat (P_lit (mk_lit (L_num (int_of_hexLit h)))), None)
  | ASL_AST.Pat_LitBits b ->
     (mk_pat (P_lit (mk_lit (L_bin (remove_spaces b)))), None)
  | ASL_AST.Pat_Const id when pprint_ident id = "TRUE" ->
     (mk_pat (P_lit (mk_lit L_true)), None)
  | ASL_AST.Pat_Const id when pprint_ident id = "FALSE" ->
     (mk_pat (P_lit (mk_lit L_false)), None)
  | ASL_AST.Pat_Const id when is_enum ctx (sail_id_of_ident id) ->
     (mk_pat (P_id (sail_id_of_ident id)), None)
  | ASL_AST.Pat_Const id ->
     let id_exp = mk_exp (E_id (sail_id_of_ident id)) in
     let var_exp = mk_exp (E_id (mk_id "?")) in
     let var_pat = mk_pat (P_id (mk_id "?")) in
     (var_pat, Some (mk_exp (E_app_infix (var_exp, mk_id "==", id_exp))))
  | ASL_AST.Pat_Wildcard ->
     (mk_pat (P_wild), None)
  | ASL_AST.Pat_LitMask lits ->
     let add_lit l pats =
       if l = '0' then mk_pat (P_lit (mk_lit L_zero)) :: pats
       else if l = '1' then mk_pat (P_lit (mk_lit L_one)) :: pats
       else if l = 'x' then mk_pat (P_wild) :: pats
       else if l = ' ' then pats
       else failwith ("Unrecognised mask literal " ^ String.make 1 l)
     in
     let pats = List.fold_right add_lit (Util.string_to_list lits) [] in
     (mk_pat (P_vector pats), None)
  | ASL_AST.Pat_Single e when is_pattern_expr e ->
     sail_of_pat ctx (pattern_of_expr e)
  | ASL_AST.Pat_Tuple _
  | ASL_AST.Pat_Set _
  | ASL_AST.Pat_Range (_, _)
  | ASL_AST.Pat_Single _ ->
     failwith ("sail_of_pat: " ^ pp_to_string (ASL_PP.pp_pattern p))

and sail_typ_arg_of_expr ctx expr =
  mk_typ_arg (A_nexp (sail_nexp_of_expr ctx expr))

and sail_int_typ_of_expr ctx exp =
  let rec sail_constraint_of_expression kid = function
    | ASL_AST.Expr_LitInt n -> nc_eq (nvar kid) (nconstant (int_of_intLit n))
    | ASL_AST.Expr_If (_, then_exp, elsifs, else_exp) ->
       nc_or (sail_constraint_of_expression kid then_exp)
             (List.fold_right
                (fun elsif constr -> nc_or (sail_constraint_of_elsif kid elsif) constr)
                elsifs (sail_constraint_of_expression kid else_exp))
    | ASL_AST.Expr_Var id -> nc_eq (nvar kid) (nvar (sail_kid_of_ident id))
    | exp -> nc_eq (nvar kid) (sail_nexp_of_expr ctx exp)
  and sail_constraint_of_elsif kid = function
    | E_Elsif_Cond (_, else_exp) -> sail_constraint_of_expression kid else_exp
  in
  let kid = mk_kid "n" in
  mk_typ (Typ_exist ([mk_kopt K_int kid], sail_constraint_of_expression kid exp, atom_typ (nvar kid)))

and sail_of_ty ctx (ty : ASL_AST.ty) =
  let recur = sail_of_ty ctx in
  match ty with
  | ASL_AST.Type_Tuple [] -> unit_typ
  | ASL_AST.Type_Tuple [ty] -> recur ty
  | ASL_AST.Type_Tuple ts -> mk_typ (Typ_tup (List.map recur ts))
  | ASL_AST.Type_Constructor id -> mk_id_typ (sail_type_id_of_ident id)
  | ASL_AST.Type_Register (i, _) -> bits_typ (nconstant (int_of_intLit i))
  | ASL_AST.Type_Bits expr -> bits_typ (nexp_simp (sail_nexp_of_expr ctx expr))
  | ASL_AST.Type_App (id, args) -> app_typ (sail_type_id_of_ident id) (List.map (sail_typ_arg_of_expr ctx) args)
  | ASL_AST.Type_Array (Index_Range (r1, r2), ty') ->
     let r1' = ASL_TC.subst_consts_expr ASL_TC.env0 r1 in
     let r2' = ASL_TC.subst_consts_expr ASL_TC.env0 r2 in
     let (len, ord) =
       match (nexp_simp (sail_nexp_of_expr ctx r1'), nexp_simp (sail_nexp_of_expr ctx r2')) with
       | (Nexp_aux (Nexp_constant i1, _), Nexp_aux (Nexp_constant i2, _)) ->
          if Big_int.greater i2 i1 then
            (nconstant (Big_int.succ i2), inc_ord)
          else
            (nconstant (Big_int.succ i1), dec_ord)
       | _ ->
          failwith ("sail_of_ty: non-constant range in " ^ pp_to_string (ASL_PP.pp_ty ty))
     in
     vector_typ len ord (recur ty')
  | ASL_AST.Type_OfExpr _
  | ASL_AST.Type_Array (_, _) -> failwith ("sail_of_ty: " ^ pp_to_string (ASL_PP.pp_ty ty))

and infer_sail_expr_typ ctx (e : ASL_AST.expr) =
  let recur = infer_sail_expr_typ ctx in
  match e with
  | Expr_Var v when Bindings.mem v ctx.locals ->
     Some (lvar_typ (Bindings.find v ctx.locals))
  | Expr_TApply (f, tes, _) ->
     Util.option_map (sail_of_ty ctx) (instantiate_fun_ret_typ f tes)
  | Expr_Tuple es ->
     begin match Util.option_all (List.map recur es) with
       | Some typs -> Some (mk_typ (Typ_tup typs))
       | None -> None
     end
  | Expr_Parens e -> recur e
  | _ -> None

and infer_sail_lexpr_typ ctx (le : ASL_AST.lexpr) =
  let recur = infer_sail_lexpr_typ ctx in
  match le with
  | LExpr_Var v when Bindings.mem v ctx.locals ->
     Some (lvar_typ (Bindings.find v ctx.locals))
  | LExpr_Write (f, tes, _) ->
     Util.option_map (sail_of_ty ctx) (instantiate_sfun_vtyp f tes)
  | LExpr_Tuple les ->
     begin match Util.option_all (List.map recur les) with
       | Some typs -> Some (mk_typ (Typ_tup typs))
       | None -> None
     end
  | _ -> None

and sail_of_stmt ctx (stmt : ASL_AST.stmt) =
  let recur = sail_of_stmt ctx in
  match stmt with
  | ASL_AST.Stmt_VarDecl (ty, id, e, _) ->
     let le = mk_lexp (LEXP_cast (sail_of_ty ctx ty, sail_id_of_ident id)) in
     mk_exp (E_assign (le, sail_of_expr ctx e))
  | ASL_AST.Stmt_Assign ((ASL_AST.LExpr_BitTuple bits as le), e, _) ->
     let e' = sail_of_expr ctx e in
     mk_exp (E_assign (sail_of_lexpr ctx le, e'))
  | ASL_AST.Stmt_Assign (LExpr_Write (f, targs, args), rhs, _) ->
     let rhs' = sail_of_expr ctx rhs in
     sail_of_setter_assignment ctx f targs args rhs'
  | ASL_AST.Stmt_Assign (LExpr_Slices (LExpr_ReadWrite (read, write, targs, args), [slice]), e, _) ->
     let implicits = instantiate_fun_implicits read targs in
     let args' = args_of_exps (List.map (sail_of_expr ctx) (implicits @ args)) in
     let e' = sail_of_expr ctx e in
     let rexp = mk_exp (E_app (sail_id_of_ident read, args')) in
     let rhs = sail_slice_update_exp ctx slice rexp e' in
     sail_of_setter_assignment ctx write targs args rhs
  | ASL_AST.Stmt_Assign (LExpr_Slices (LExpr_Var v, [slice]), e, _)
    when is_number_local ctx v || is_slice_lowd slice ->
     let v' = sail_id_of_ident v in
     let e' = sail_of_expr ctx e in
     let rhs = sail_slice_update_exp ctx slice (mk_exp (E_id v')) e' in
     mk_exp (E_assign (mk_lexp (LEXP_id v'), rhs))
  | ASL_AST.Stmt_Assign (LExpr_Slices (LExpr_Var v, [Slice_Single idx]), e, _)
    when is_bits_local ctx v ->
     let v' = sail_id_of_ident v in
     let idx' = sail_of_expr ctx idx in
     let e' = mk_exp (E_app (mk_id "Bit", [sail_of_expr ctx e])) in
     mk_exp (E_assign (mk_lexp (LEXP_vector (mk_lexp (LEXP_id v'), idx')), e'))
  | ASL_AST.Stmt_Assign (LExpr_Tuple lexps, e, _)
    when List.exists has_setter_lexpr lexps ->
     sail_of_tuple_assignment ctx lexps e
  | ASL_AST.Stmt_Assign (le, e, _) ->
     mk_exp (E_assign (sail_of_lexpr ctx le, sail_of_expr ctx e))
  | ASL_AST.Stmt_FunReturn (e, _) ->
     mk_exp (E_return (sail_of_expr ctx e))
  | ASL_AST.Stmt_ProcReturn _ ->
     mk_exp (E_return (mk_lit_exp L_unit))
  | ASL_AST.Stmt_Assert (e, l) ->
     mk_exp (E_assert (sail_of_expr ctx e, mk_lit_exp (L_string "")))
  | ASL_AST.Stmt_TCall (abort, _, [], _) when name_of_ident abort = "__abort" ->
     mk_exp (E_exit (mk_lit_exp L_unit))
  | ASL_AST.Stmt_TCall (id, _, args, _) ->
     mk_exp (E_app (sail_id_of_ident id, args_of_exps (List.map (sail_of_expr ctx) args)))
  | ASL_AST.Stmt_If (c, t, eifs, e, l) ->
     let t_exp = sail_of_stmts ctx t in
     let e_exp =
       match eifs with
       | [] -> sail_of_stmts ctx e
       | S_Elsif_Cond (c', t') :: eifs ->
          recur (ASL_AST.Stmt_If (c', t', eifs, e, l))
     in
     mk_exp (E_if (sail_of_expr ctx c, t_exp, e_exp))
  | ASL_AST.Stmt_Case (e, alts, otherwise, _) ->
     let alts' = List.concat (List.map (sail_of_alt ctx) alts) in
     let otherwise' =
       match otherwise with
       | Some stmts ->
          [mk_pexp (Pat_exp (mk_pat P_wild, sail_of_stmts ctx stmts))]
       | None ->
          let pc_ctx = Type_check.Env.pattern_completeness_ctx ctx.tc_env in
          if Pattern_completeness.is_complete pc_ctx alts' then [] else
          [mk_pexp (Pat_exp (mk_pat P_wild, sail_of_stmts ctx []))]
     in
     mk_exp (E_case (sail_of_expr ctx e, alts' @ otherwise'))
  | ASL_AST.Stmt_For (var, start, dir, stop, stmts, l) ->
     let var' = sail_id_of_ident var in
     let start' = sail_of_expr ctx start in
     let dir' =
       match dir with
       | Direction_Up -> inc_ord
       | Direction_Down -> dec_ord
     in
     let stop' = sail_of_expr ctx stop in
     let step = mk_lit_exp (L_num (Big_int.of_int 1)) in
     let ctx' = share_locals (IdentSet.inter (fv_stmts stmts) (assigned_vars_of_stmts stmts)) ctx in
     let stmts' = sail_of_stmts ~force_block:true ctx' stmts in
     mk_exp (E_for (var', start', stop', step, dir', stmts'))
  | ASL_AST.Stmt_While (e, stmts, l) ->
     let e' = sail_of_expr ctx e in
     let ctx' = share_locals (IdentSet.inter (fv_stmts stmts) (assigned_vars_of_stmts stmts)) ctx in
     let stmts' = sail_of_stmts ~force_block:true ctx' stmts in
     mk_exp (E_loop (While, measure_none, e', stmts'))
  | ASL_AST.Stmt_Repeat (stmts, e, l) ->
     let e' = sail_of_expr ctx e in
     let ctx' = share_locals (IdentSet.inter (fv_stmts stmts) (assigned_vars_of_stmts stmts)) ctx in
     let stmts' = sail_of_stmts ~force_block:true ctx' stmts in
     mk_exp (E_loop (Until, measure_none, e', stmts'))
  | ASL_AST.Stmt_Undefined _ | ASL_AST.Stmt_Dep_Undefined _ ->
     mk_exp (E_throw (mk_exp (E_app (mk_id "Error_Undefined", [mk_lit_exp L_unit]))))
  | ASL_AST.Stmt_Unpred _ | ASL_AST.Stmt_Dep_Unpred _ ->
     mk_exp (E_throw (mk_exp (E_app (mk_id "Error_Unpredictable", [mk_lit_exp L_unit]))))
  | ASL_AST.Stmt_ConstrainedUnpred _ ->
     mk_exp (E_throw (mk_exp (E_app (mk_id "Error_ConstrainedUnpredictable", [mk_lit_exp L_unit]))))
  | ASL_AST.Stmt_ImpDef (id, _) ->
     let id' = mk_lit_exp (L_string (name_of_ident id)) in
     mk_exp (E_throw (mk_exp (E_app (mk_id "Error_ImplementationDefined", [id']))))
  | ASL_AST.Stmt_Dep_ImpDef (id, _) ->
     let id' = mk_lit_exp (L_string id) in
     mk_exp (E_throw (mk_exp (E_app (mk_id "Error_ImplementationDefined", [id']))))
  | ASL_AST.Stmt_See (e, _) ->
     let str =
       match e with
       | Expr_LitString str -> str
       | _ -> string_of_exp (sail_of_expr ctx e)
     in
     let e' = mk_lit_exp (L_string str) in
     mk_exp (E_throw (mk_exp (E_app (mk_id "Error_See", [e']))))
  | ASL_AST.Stmt_Try (stmts, exid, catchers, fallthrough, _) ->
     let stmts' = sail_of_stmts ctx stmts in
     let fallthrough' =
       match fallthrough with
       | Some stmts -> [mk_pexp (Pat_exp (mk_pat P_wild, sail_of_stmts ctx stmts))]
       | None -> []
     in
     let catchers' = List.map (sail_pexp_of_catcher ctx exid) catchers in
     mk_exp (E_try (stmts', catchers' @ fallthrough'))
  | ASL_AST.Stmt_ExceptionTaken _ ->
     mk_exp (E_throw (mk_exp (E_app (mk_id "Error_ExceptionTaken", [mk_lit_exp L_unit]))))
  | ASL_AST.Stmt_DecodeExecute (arch, instr, l) ->
     let decoder = prepend_id "Execute" (sail_id_of_ident arch) in
     mk_exp (E_app (decoder, [sail_of_expr ctx instr]))
  | ASL_AST.Stmt_VarDeclsNoInit (_, _, _)
  | ASL_AST.Stmt_ConstDecl (_, _, _, _)
  | ASL_AST.Stmt_Throw (_, _) ->
     failwith ("sail_of_stmt: " ^ pp_to_string (ASL_PP.pp_stmt stmt))

and sail_of_alt ctx (Alt_Alt (pats, guard, stmts)) =
  let guard' = Util.option_map (sail_of_expr ctx) guard in
  let stmts' = sail_of_stmts ctx stmts in
  let pexp_of_pat (pat, pguard) =
    construct_pexp (pat, combine_guards "&" pguard guard') stmts'
  in
  List.map pexp_of_pat (List.map (sail_of_pat ctx) pats)

and sail_pexp_of_catcher ctx exid (ASL_AST.Catcher_Guarded (guard, stmts)) =
  let pat = mk_pat (P_id (sail_id_of_ident exid)) in
  let guard' = sail_of_expr ctx guard in
  let stmts' = sail_of_stmts ctx stmts in
  mk_pexp (Pat_when (pat, guard', stmts'))

and sail_block_of_stmts (ctx : ctx) (stmts : ASL_AST.stmt list) : unit exp list =
  match stmts with
  | ASL_AST.Stmt_VarDeclsNoInit (ty, ids, _) :: stmts ->
     let ty' = sail_of_ty ctx ty in
     let constraints = int_constraints_of_stmts stmts in
     let decl id =
       let (ty', e') =
         if ty = ASL_TC.type_integer && IdentSet.mem id (initialised_vars stmts)
            && Bindings.mem id constraints then
           (sail_typ_of_int_constraint id (Bindings.find id constraints),
            initial_exp_of_int_constraint (Bindings.find id constraints))
         else (ty', mk_lit_exp L_undef)
       in
       let id' = sail_id_of_ident id in
       mk_exp (E_assign (mk_lexp (LEXP_cast (ty', id')), e'))
     in
     let decls =
       List.filter (fun id -> initial_assignment id stmts = None) ids
       |> List.map decl
     in
     decls @ sail_block_of_stmts ctx stmts
  | (ASL_AST.Stmt_VarDecl (ty, id, e, _) as stmt) :: stmts ->
     let e' = sail_of_expr_rebinds ctx (constrained_vars_of_stmts ctx [stmt]) e in
     if IdentSet.mem id (assigned_vars_of_stmts stmts) then
       let constraints = int_constraints_of_stmts (stmt :: stmts) in
       let ty' =
         if Bindings.mem id constraints then
           match Bindings.find id constraints with
           | IC_Unknown -> local_typ ctx id
           | c -> sail_typ_of_int_constraint id c
         else local_typ ctx id
       in
       let le = mk_lexp (LEXP_cast (ty', sail_id_of_ident id)) in
       mk_exp (E_assign (le, e')) :: sail_block_of_stmts ctx stmts
     else
       (* Bind variables that are not modified (any more) as immutables *)
       sail_letbind_stmts ctx (sail_of_ty ctx ty) id e' stmts
  | (ASL_AST.Stmt_Assign (LExpr_Var id, e, _) as stmt) :: stmts
    when is_owned_local ctx id && IdentSet.mem id (fv_stmts stmts) ->
     let e' = sail_of_expr_rebinds ctx (constrained_vars_of_stmts ctx [stmt]) e in
     if IdentSet.mem id (assigned_vars_of_stmts stmts) then
       let constraints = int_constraints_of_stmts (stmt :: stmts) in
       let ty' =
         if Bindings.mem id constraints then
           match Bindings.find id constraints with
           | IC_Unknown -> local_typ ctx id
           | c -> sail_typ_of_int_constraint id c
         else local_typ ctx id
       in
       let id' = sail_id_of_ident id in
       mk_exp (E_assign (mk_lexp (LEXP_cast (ty', id')), e'))
       :: sail_block_of_stmts ctx stmts
     else
       sail_letbind_stmts ctx (local_typ ctx id) id e' stmts
  | ASL_AST.Stmt_ConstDecl (ty, id, e, l) :: stmts ->
     let id' = sail_id_of_ident id in
     let pat =
       if ty = ASL_TC.type_integer then int_var_pat id' else
       mk_pat (P_typ (sail_of_ty ctx ty, mk_pat (P_id id')))
     in
     let typ = if ty = ASL_TC.type_integer then int_var_typ id' else sail_of_ty ctx ty in
     let ctx' = declare_immutable id typ ctx in
     [mk_exp (E_let (mk_letbind pat (sail_of_expr ctx e), sail_of_stmts ctx' stmts))]
  | ASL_AST.Stmt_Assign (LExpr_Slices ((LExpr_ReadWrite _ as lexp), slices), e, l) :: stmts
    when List.for_all const_width_slice slices && List.length slices > 1 ->
     sail_block_of_slice_assignments ctx lexp slices e l
     @ sail_block_of_stmts ctx stmts
  | [stmt] when not (needs_rebind ctx stmt) ->
     [sail_of_stmt ctx stmt]
  | stmt :: stmts ->
     (* Mark variables that are used in the rest of the block as shared
        while translating the current statement *)
     let stmt_ctx = share_locals (fv_stmts stmts) ctx in
     (* Re-bind mutable variables that might appear in type annotations *)
     let constrained_muts = constrained_vars_of_stmts ctx [stmt] in
     let stmt' = sail_of_stmt_rebinds stmt_ctx constrained_muts stmt in
     (* Re-bind variables that are modified the last time as immutables after stmt *)
     let new_immutables =
       IdentSet.diff (assigned_vars_of_stmts [stmt]) (assigned_vars_of_stmts stmts)
       |> IdentSet.filter (is_number_local ctx)
       |> IdentSet.filter (is_owned_local ctx)
       |> IdentSet.inter (fv_stmts stmts)
     in
     let stmts' = sail_block_of_stmts_rebinds ctx new_immutables stmts in
     stmt' :: stmts'
  | [] ->
     [mk_lit_exp L_unit]

and sail_block_of_slice_assignments ctx lexp slices rhs l =
  match slices with
  | slice :: rest ->
     let width_slice = int_of_slice_width slice in
     let width_rest =
       List.map int_of_slice_width rest
       |> List.fold_left Big_int.add Big_int.zero
     in
     let lo = Expr_LitInt (Big_int.to_string width_rest) in
     let wd = Expr_LitInt (Big_int.to_string width_slice) in
     let rhs' = Expr_Slices (rhs, [Slice_LoWd (lo, wd)]) in
     sail_of_stmt ctx (ASL_AST.Stmt_Assign (ASL_AST.LExpr_Slices (lexp, [slice]), rhs', l))
     :: sail_block_of_slice_assignments ctx lexp rest rhs l
  | [] -> []

and sail_letbind_exp ctx (typ : typ) id bind exp =
  let id' = sail_id_of_ident id in
  let pat =
    if typ = int_typ then int_var_pat id'
    else mk_pat (P_typ (typ, mk_pat (P_id id')))
  in
  mk_exp (E_let (mk_letbind pat bind, exp))

and sail_letbind_stmts ctx typ id bind stmts =
  let ctx' = declare_immutable id typ ctx in
  let stmts' = sail_of_stmts ~force_block:true ctx' stmts in
  [sail_letbind_exp ctx typ id bind stmts']

and sail_of_stmts ?force_block:(fb=false) ctx = function
  (* | [stmt] when not(fb) && not (needs_rebind ctx stmt) ->
     sail_of_stmt ctx stmt *)
  | [] when not(fb) ->
     mk_lit_exp L_unit
  | stmts ->
     let locals' =
       locals_of_stmts stmts
       |> Bindings.map (sail_of_ty ctx)
       |> Bindings.map mk_lvar
     in
     let ctx' = { ctx with locals = merge_bindings locals' ctx.locals} in
     mk_exp (E_block (sail_block_of_stmts ctx' stmts))

and sail_rebind_int ctx id exps =
  let id' = sail_id_of_ident id in
  [sail_letbind_exp ctx int_typ id (mk_exp (E_id id')) (mk_exp (E_block exps))]

and sail_rebind_ints ctx ids exps =
  IdentSet.fold (sail_rebind_int ctx) ids exps

and sail_block_of_stmts_rebinds ctx ids stmts =
  let ctx' = IdentSet.fold redeclare_immutable ids ctx in
  let stmts' = sail_block_of_stmts ctx' stmts in
  sail_rebind_ints ctx ids stmts'

and sail_of_stmt_rebinds ctx ids stmt =
  let ctx' = IdentSet.fold redeclare_immutable ids ctx in
  let stmt' = sail_of_stmt ctx' stmt in
  match sail_rebind_ints ctx ids [stmt'] with
  | [stmt''] -> stmt''
  | exps -> mk_exp (E_block exps)

and sail_of_expr_rebinds ctx ids expr =
  let ctx' = IdentSet.fold redeclare_immutable ids ctx in
  let expr' = sail_of_expr ctx' expr in
  match sail_rebind_ints ctx ids [expr'] with
  | [expr''] -> expr''
  | exps -> mk_exp (E_block exps)

let constraints_of_fun id body =
  let tvs = match get_asl_funtype id with
    | Some (_, _, _, _, args, rty) -> IdentSet.union (fv_args args) (fv_type rty)
    | None -> IdentSet.empty
  in
  let rec constraints_of_stmts = function
    | [] -> []
    | Stmt_VarDeclsNoInit (_, ids, _) :: stmts
      when List.for_all (fun id -> not (IdentSet.mem id tvs)) ids ->
       constraints_of_stmts stmts
    | (Stmt_VarDecl (_, id, _, _) | Stmt_ConstDecl (_, id, _, _)) :: stmts
      when not (IdentSet.mem id tvs) ->
       constraints_of_stmts stmts
    | Stmt_Assert (expr, _) :: stmts when IdentSet.subset (fv_expr expr) tvs ->
       let c = try [sail_n_constraint_of_expr empty_ctx expr] with _ -> [] in
       c @ constraints_of_stmts stmts
    | Stmt_Assert (expr, _) :: stmts ->
       constraints_of_stmts stmts
    | _ -> []
  in
  constraints_of_stmts body

let get_fun_constraints decls =
  let add_decl constraints decl = match decl with
    | Decl_FunDefn (_, id, _, stmts, _)
    | Decl_ProcDefn (id, _, stmts, _)
    | Decl_VarGetterDefn (_, id, stmts, _)
    | Decl_VarSetterDefn (id, _, _, stmts, _)
    | Decl_ArrayGetterDefn (_, id, _, stmts, _)
    | Decl_ArraySetterDefn (id, _, _, _, stmts, _) ->
       begin match constraints_of_fun id stmts with
         | [] -> constraints
         | cs -> Bindings.add id (List.fold_left nc_and nc_true cs) constraints
       end
    | _ -> constraints
  in
  List.fold_left add_decl Bindings.empty decls

let sail_typschm_of_funtype ?ncs:(ncs=[]) ctx id ret_ty args =
  let ret_ty' = sail_of_ty ctx ret_ty in
  let typ_of_arg (ty, id) =
    let kid = kid_of_id (sail_id_of_ident id) in
    match ty with
    | ASL_AST.Type_Constructor integer
      when name_of_ident integer = "integer" ->
       ([mk_kopt K_int kid], atom_typ (nvar kid))
    | ASL_AST.Type_Constructor boolean
      when name_of_ident boolean = "boolean" ->
       ([mk_kopt K_bool kid], atom_bool_typ (nc_var kid))
    | _ -> ([], sail_of_ty ctx ty)
  in
  (* Add any variables that occur only in the return type as implicits *)
  let implicit_typ id = implicit_typ (nvar (kid_of_id (sail_id_of_ident id))) in
  let implicit_typs = List.map implicit_typ (get_fun_implicits id) in
  let (kopts, arg_typs) =
    if args = [] && implicit_typs = [] then ([], [unit_typ]) else
    List.split (List.map typ_of_arg args)
  in
  let quants =
    List.concat kopts @ kopts_of_funtype ctx ret_ty args
    |> KOptSet.of_list |> KOptSet.elements |> List.map mk_qi_kopt
  in
  (* Add constraints extracted from function body as well as explicitly passed constraints *)
  let fun_ncs = try [Bindings.find id ctx.fun_constraints] with Not_found -> [] in
  let nc_qis = match fun_ncs @ ncs with
    | [] -> []
    | ncs -> [mk_qi_nc (List.fold_left nc_and nc_true ncs)]
  in
  let tq = mk_typquant (quants @ nc_qis) in
  mk_typschm tq (function_typ (implicit_typs @ arg_typs) ret_ty' no_effect)

let sail_valspec_of_decl ?ncs:(ncs=[]) ctx id ret_ty args =
  let id' = sail_id_of_ident id in
  let typschm = sail_typschm_of_funtype ~ncs:ncs ctx id ret_ty args in
  [mk_val_spec (VS_val_spec (typschm, id', [], false))]

let sail_fundef_of_decl ctx id ret_ty args stmts =
  let id' = sail_id_of_ident id in
  (* Add any variables that occur only in the return type as implicits *)
  let implicit_arg v = (Type_Constructor (Ident ("implicit")), v) in
  let args = List.map implicit_arg (get_fun_implicits id) @ args in
  let arg_ids = IdentSet.of_list (List.map snd args) in
  (* ASL allows modification of function arguments, unlike Sail.
     Hence, we re-bind modified arguments as mutable variables. *)
  let is_mutated (ty, v) = IdentSet.mem v (assigned_vars_of_stmts stmts) in
  let pat_of_arg (ty, v) =
    let v' = sail_id_of_ident v in
    mk_pat (P_id (if is_mutated (ty, v) then append_id v' "__arg" else v'))
  in
  let mutated_decl (ty, v) =
    let v' = sail_id_of_ident v in
    let arg_id = append_id v' "__arg" in
    let ty' = sail_of_ty ctx ty in
    mk_exp (E_assign (mk_lexp (LEXP_cast (ty', v')), mk_exp (E_id arg_id)))
  in
  let mutated_decls = List.filter is_mutated args |> List.map mutated_decl in
  let add_mutated_decls body =
    match (mutated_decls, body) with
    | ([], _) -> body
    | (_, E_aux (E_block exps, _)) -> mk_exp (E_block (mutated_decls @ exps))
    | (_, _) -> mk_exp (E_block (mutated_decls @ [body]))
  in
  let pat =
    match List.map pat_of_arg args with
    | [] -> mk_pat (P_lit (mk_lit L_unit))
    | [p] -> p
    | ps -> mk_pat (P_tup ps)
  in
  (* Letbind calls to getter function for global type variables *)
  let stmts = rewrite_pl stmts in
  let vl_bindings =
    vl_exprs_of_stmts false stmts
    |> List.filter (fun (_, id, _, _) -> not (IdentSet.mem id arg_ids))
  in
  let bind_vl_exp (_, id, expr, _) exp =
    let lhs = int_var_pat (sail_id_of_ident id) in
    let rhs = sail_of_expr ctx expr in
    mk_exp (E_block [mk_exp (E_let (mk_letbind lhs rhs, exp))])
  in
  let add_vl_ctx ctx (key, id, _, _) =
    { ctx with bound_exprs = ExprMap.add key id ctx.bound_exprs }
  in
  let ctx = List.fold_left add_vl_ctx ctx vl_bindings in
  (* Add arguments to context *)
  let declare_arg (ty, id) ctx = declare_immutable id (sail_of_ty ctx ty) ctx in
  let ctx' =
    { ctx with fun_args = args }
    |> List.fold_right declare_arg args
  in
  (* For functions, add final return statements to all branches.
     Otherwise, there might be branches that end with a call to
     EndOfInstruction() or similar, and it is not clear to the Sail
     typechecker that this removes the need for returning a value
     in that branch. *)
  let is_proc = (ret_ty = ASL_TC.type_unit) in
  let body =
    (if is_proc then stmts else add_final_return_stmt ret_ty stmts)
    |> sail_of_stmts ~force_block:true ctx'
    |> add_mutated_decls
    |> List.fold_right bind_vl_exp vl_bindings
  in
  [mk_fundef [mk_funcl id' pat body]]

let is_out_sformal = function
  | ASL_AST.Formal_In (_, _) -> false
  | ASL_AST.Formal_InOut (_, _) -> true

let arg_of_sformal (sf : ASL_AST.sformal) =
  match sf with
  | ASL_AST.Formal_In (ty, id) -> (ty, id)
  | ASL_AST.Formal_InOut (ty, id) -> (ty, id)

let index_range_of_slice ctx = function
  | Slice_Single e ->
      BF_aux (BF_single (sail_nexp_of_expr ctx e), Parse_ast.Unknown)
  | Slice_HiLo (hi, lo) ->
      let hi' = sail_nexp_of_expr ctx hi in
      let lo' = sail_nexp_of_expr ctx lo in
      BF_aux (BF_range (hi', lo'), Parse_ast.Unknown)
  | Slice_LoWd (start, len) ->
      let lo = sail_nexp_of_expr ctx start in
      let len' = sail_nexp_of_expr ctx len in
      let hi = nexp_simp (nsum lo (nminus len' (nconstant (Big_int.of_int 1)))) in
      BF_aux (BF_range (hi, lo), Parse_ast.Unknown)

let rec index_range_of_slices ctx = function
  | [slice] -> index_range_of_slice ctx slice
  | slice :: slices ->
     let slice' = index_range_of_slice ctx slice in
     let slices' = index_range_of_slices ctx slices in
     BF_aux (BF_concat (slice', slices'), Parse_ast.Unknown)
  | [] ->
     failwith "index_range_of_slices"

let sail_bitfield_of_regtype ctx id len fields =
  let len' = int_of_intLit len in
  let fields' =
    List.map
      (fun (slices, id) -> (sail_id_of_ident id, index_range_of_slices ctx slices))
      fields
  in
  DEF_type (TD_aux (TD_bitfield (id, bits_typ (nconstant len'), fields'), no_annot))

let and_bool_opt exp1 exp2 = match (exp1, exp2) with
  | (Some exp, None) | (None, Some exp) -> Some exp
  | (Some exp1, Some exp2) -> Some (mk_exp (E_app_infix (exp1, mk_id "&", exp2)))
  | (None, None) -> None

let decoder_num = ref Big_int.zero

(* Generate clause for the global decode function
   TODO: Add back optional generation and use of an AST datatype
 *)
let sail_decoder_clause ctx = function
  | (ASL_AST.Encoding_Block (id, arch, fields, opcode, guard, unpreds, stmts, l)) ->
     let (pat, pguard) = match opcode with
       | Opcode_Bits b -> sail_of_pat ctx (Pat_LitBits b)
       | Opcode_Mask m -> sail_of_pat ctx (Pat_LitMask m)
     in
     (* TODO: Check for fields that are constant in the opcode and propagate those constants? *)
     let getter = function
       | IField_Field (id, start, len) ->
          let start' = mk_lit_exp (L_num (Big_int.of_int start)) in
          let len' = mk_lit_exp (L_num (Big_int.of_int len)) in
          let opcode' = mk_exp (E_id (mk_id "opcode")) in
          (sail_id_of_ident id, mk_exp (E_app (mk_id "Slice", [opcode'; start'; len'])))
     in
     let getters = List.map getter fields in
     let guard' = match sail_of_expr ctx guard with
       | E_aux (E_lit (L_aux (L_true, _)), _) -> None
       | exp ->
          let subst_field exp (id, getter) = subst id getter exp in
          Some (List.fold_left subst_field exp getters)
     in
     decoder_num := Big_int.succ !decoder_num;
     let see_check = mk_exp (E_app_infix (mk_exp (E_id (mk_id "SEE")), mk_id "<", mk_lit_exp (L_num !decoder_num))) in
     let see_update = mk_exp (E_assign (mk_lexp (LEXP_id (mk_id "SEE")), mk_lit_exp (L_num !decoder_num))) in
     let clause_guard = and_bool_opt (and_bool_opt guard' pguard) (Some see_check) in
     let decode_id = add_name_prefix "decode" id in
     let decode_args = List.map (fun (IField_Field (id, _, _)) -> Expr_Var id) fields in
     let decode_call = Stmt_TCall (decode_id, [], decode_args, Unknown) in
     let unpred_check (idx, value) =
       let idx' = Expr_LitInt (string_of_int idx) in
       let bit = Expr_Slices (Expr_Var (Ident "opcode"), [Slice_Single idx']) in
       Expr_Binop (bit, Binop_NtEq, Expr_LitBits value)
     in
     let decode_stmt = match List.map unpred_check unpreds with
       | [] -> decode_call
       | check :: checks ->
          let or_expr e1 e2 = Expr_Binop (e1, Binop_BoolOr, e2) in
          let cond = List.fold_left or_expr check checks in
          Stmt_If (cond, [Stmt_ConstrainedUnpred Unknown], [], [decode_call], Unknown)
     in
     let decode_stmt' = sail_of_stmt ctx decode_stmt in
     let bind_field (id, getter) exp =
       mk_exp (E_let (mk_letbind (mk_pat (P_id id)) getter, mk_exp (E_block [exp])))
     in
     let body = mk_exp (E_block [see_update; List.fold_right bind_field getters decode_stmt']) in
     let clause_pat = mk_pat (P_tup [mk_pat (P_id (mk_id "pc")); mk_pat (P_as (pat, mk_id "opcode"))]) in
     let pexp = construct_pexp (clause_pat, clause_guard) body in
     let decoder_id = mk_id ("__Decode" ^ pprint_ident arch) in
     let sdfuncl = SD_funcl (FCL_aux (FCL_Funcl (decoder_id, pexp), no_annot)) in
     [DEF_scattered (SD_aux (sdfuncl, no_annot))]

let sail_of_encoding ctx opost exec_id vl_exprs exec_args conditional encoding =
  match encoding with
  | (ASL_AST.Encoding_Block (id, arch, fields, opcode, guard, unpreds, stmts, l)) ->
     let decode_id = add_name_prefix "decode" id in
     let args = List.map arg_of_ifield fields in
     let post = Util.option_default [] opost in
     let decode_body = stmts @ post in
     let arg_missing (_, v) =
       not (Bindings.mem v (locals_of_stmts decode_body))
       && not (List.exists (fun (_, v') -> Id.compare v v' = 0) args)
     in
     let decode_body = match List.filter arg_missing exec_args with
       | [] -> decode_body
       | missing -> List.map (fun (ty, v) -> Stmt_VarDeclsNoInit (ty, [v], l)) missing @ decode_body
     in
     let exec_args' = List.map (fun (_, v) -> Expr_Var v) exec_args in
     let constraints = int_constraints_of_stmts decode_body in
     let constraints = int_constraints_of_stmts ~known_vars:constraints decode_body in
     let split_vls stmt =
       if !mono_vl && List.exists is_vl_read vl_exprs then
         let vl_call = Expr_TApply (vl_read_id, [], []) in
         let alt vl =
           let vl' = string_of_int vl in
           let call' = subst_vl vl [stmt] in
           Alt_Alt ([Pat_LitInt vl'], None, call')
         in
         Stmt_Case (vl_call, List.map alt !implemented_vls, None, l)
       else stmt
     in
     let split_var var stmt =
       let error_msg = "Failed to split variable " ^ name_of_ident var ^ " in decode " ^ name_of_ident id in
       match Bindings.find var constraints with
       | IC_Set is ->
          let fail_stmt = Stmt_Assert (Expr_Var (Ident "FALSE"), l) in
          let alt i =
            let i' = Big_int.to_string i in
            let subst = Bindings.singleton var (Expr_LitInt i') in
            Alt_Alt ([Pat_LitInt i'], None, subst_stmts subst [stmt])
          in
          Stmt_Case (Expr_Var var, List.map alt (BigIntSet.elements is), Some [fail_stmt], l)
       | _ -> failwith error_msg
       | exception _ -> failwith error_msg
     in
     let exec_call =
       Stmt_TCall (exec_id, [], vl_exprs @ exec_args', l)
       |> split_vls
       |> List.fold_right split_var (get_mono_splits (stripTag id))
     in
     let body = decode_body @ [exec_call] |> rewrite_pl in
     let cond_body =
       if conditional then
         [Stmt_If (Expr_TApply (Ident "ConditionPassed", [], []), body, [], [], Unknown)]
       else body
     in
     sail_valspec_of_decl ctx decode_id unit_ty args @
     sail_fundef_of_decl ctx decode_id unit_ty args cond_body @
     sail_decoder_clause ctx encoding

let initialise_vars (ics : int_constraint Bindings.t) stmts =
  let rec rewrite = function
    | Stmt_VarDeclsNoInit (ty, ids, l) :: stmts ->
       let init_vars = List.filter (fun id -> Bindings.mem id ics) ids in
       let initialise id =
         match initial_expr_of_int_constraint (Bindings.find id ics) with
         | Some expr -> [Stmt_Assign (LExpr_Var id, expr, l)]
         | None -> []
       in
       let init_exprs = List.concat (List.map initialise init_vars) in
       Stmt_VarDeclsNoInit (ty, ids, l) :: init_exprs @ (rewrite stmts)
    | stmt :: stmts -> stmt :: rewrite stmts
    | [] -> []
  in
  rewrite stmts

let sail_of_declaration ctx (decl : ASL_AST.declaration) =
  (* PPrint.ToChannel.pretty 1. 120 stderr (ASL_PP.pp_declaration decl); *)
  match decl with
  | Decl_Record (id, fields, l) ->
     let id' = sail_type_id_of_ident id in
     let field' (ty, id) = (sail_of_ty ctx ty, sail_id_of_ident id) in
     let tvars = ASL_Utils.unionSets (List.map (fun (ty, _) -> ASL_Utils.fv_type ty) fields) in
     let tq = mk_typquant (List.map mk_qi_kopt (kopts_of_vars ctx tvars)) in
     [DEF_type (TD_aux (TD_record (id', tq, List.map field' fields, false), no_annot))]
  (* TODO
     It turns out that asli already desugars bitfield accesses, so we can
     just treat bitfields as bitvectors (which the fallthrough cases below
     will do).  However, it would be nicer to preserve that sugar and use
     Sail's bitfield support.  This would require changes in asli to not
     desugar bitfields (or resugar after typechecking), and changes in the
     translation to insert coercions between Sail bitfield types and
     bitvectors (in ASL one can be used in place of the other).

  | Decl_Typedef (id, Type_Register (len, ((_ :: _) as fields)), l) ->
     [sail_bitfield_of_regtype ctx (sail_type_id_of_ident id) len fields]
  | Decl_Var (Type_Register (len, ((_ :: _) as fields)), id, l) ->
     let id' = sail_id_of_ident id in
     let typ_id = append_id id' "_bitfield" in
     let rreg = mk_effect [BE_rreg] in
     let wreg = mk_effect [BE_wreg] in
     sail_bitfield_of_regtype ctx typ_id len fields ::
     [DEF_reg_dec (DEC_aux (DEC_reg (rreg, wreg, mk_id_typ typ_id, id'), no_annot))]*)
  | Decl_Typedef (id, ty, l) ->
     let id' = sail_type_id_of_ident id in
     let ty' = sail_of_ty ctx ty in
     let kopts = kopts_of_vars ctx (ASL_Utils.fv_type ty) in
     let tq = mk_typquant (List.map mk_qi_kopt kopts) in
     [DEF_type (TD_aux (TD_abbrev (id', tq, arg_typ ty'), no_annot))]
  | Decl_Enum (id, ids, l) ->
     let id' = sail_type_id_of_ident id in
     let ids' = List.map sail_id_of_ident ids in
     [DEF_type (TD_aux (TD_enum (id', ids', false), no_annot))]
  | Decl_Var (ty, id, l) ->
     let id' = sail_id_of_ident id in
     let ty' = sail_of_ty ctx ty in
     let rreg = mk_effect [BE_rreg] in
     let wreg = mk_effect [BE_wreg] in
     [DEF_reg_dec (DEC_aux (DEC_reg (rreg, wreg, ty', id'), no_annot))]
  | Decl_Config (ty, id, e, l) ->
     let id' = sail_id_of_ident id in
     let ty' = sail_of_ty ctx ty in
     let e' = sail_of_expr ctx e in
     [DEF_reg_dec (DEC_aux (DEC_config (id', ty', e'), no_annot))]
  | Decl_Const (ty, id, e, l) ->
     let id' = sail_id_of_ident id in
     let (ty', tydef) =
       if ty = ASL_TC.type_integer then
         try
           let nexp = sail_nexp_of_expr ctx e in
           (atom_typ nexp,
            [DEF_type (TD_aux (TD_abbrev (id', mk_typquant [], arg_nexp nexp), no_annot))])
         with _ -> (sail_of_ty ctx ty, [])
       else (sail_of_ty ctx ty, [])
     in
     let pat = mk_pat (P_typ (ty', mk_pat (P_id id'))) in
     [DEF_val (mk_letbind pat (sail_of_expr ctx e))] @ tydef
  | Decl_FunType (ret_ty, id, args, l)
  | Decl_BuiltinFunction (ret_ty, id, args, l)
  | Decl_ArrayGetterType (ret_ty, id, args, l) ->
     sail_valspec_of_decl ctx id ret_ty args
  | Decl_ArrayGetterDefn (ret_ty, id, args, stmts, l) ->
     sail_fundef_of_decl ctx id ret_ty args stmts
  | Decl_VarGetterType (ty, id, l) ->
     sail_valspec_of_decl ctx id ty []
  | Decl_VarGetterDefn (ty, id, stmts, l) ->
     sail_fundef_of_decl ctx id ty [] stmts
  | Decl_VarSetterType (id, ty, arg, l) ->
     sail_valspec_of_decl ctx id unit_ty [(ty, arg)]
  | Decl_VarSetterDefn (id, ty, arg, stmts, l) ->
     sail_fundef_of_decl ctx id unit_ty [(ty, arg)] stmts
  | Decl_ProcType (id, args, l) ->
     sail_valspec_of_decl ctx id unit_ty args
  | Decl_ArraySetterType (id, args, ty, var, l) ->
     let in_args = List.map arg_of_sformal args @ [(ty, var)] in
     let ret_tys = List.filter is_out_sformal args |> List.map arg_of_sformal |> List.map fst in
     let ret_ty =
       match ret_tys with
       | [] -> unit_ty
       | [ty] -> ty
       | tys -> Type_Tuple tys
     in
     sail_valspec_of_decl ctx id ret_ty in_args
  | Decl_ArraySetterDefn (id, args, ty, var, stmts, l) ->
     let in_args = List.map arg_of_sformal args @ [(ty, var)] in
     let ret_tys = List.filter is_out_sformal args |> List.map arg_of_sformal |> List.map fst in
     let ret_ty =
       match ret_tys with
       | [] -> unit_ty
       | [ty] -> ty
       | tys -> Type_Tuple tys
     in
     let stmts' =
       match List.filter is_out_sformal args |> List.map arg_of_sformal with
       | [] -> stmts
       | out_args ->
          let ret_exp =
            match List.map (fun (_, v) -> Expr_Var v) out_args with
            | [e] -> e
            | es -> Expr_Tuple es
          in
          let replaceReturn = function
            | Stmt_ProcReturn l -> Some (Stmt_FunReturn (ret_exp, l))
            | _ -> None
          in
          let repl = new replaceStmtClass replaceReturn in
          LibASL.Asl_visitor.visit_stmts repl stmts
     in
     sail_fundef_of_decl ctx id ret_ty in_args stmts'
  | Decl_FunDefn (ret_ty, id, args, stmts, _) ->
     sail_fundef_of_decl ctx id ret_ty args stmts
  | Decl_ProcDefn (id, args, stmts, _) ->
     sail_fundef_of_decl ctx id unit_ty args stmts
  | Decl_InstructionDefn (id, encodings, opost, conditional, exec, l) ->
     let postbindings =
       match opost with
       | Some post -> locals_of_stmts post
       | _ -> Bindings.empty
     in
     let bindings =
       List.map locals_of_encoding encodings
       |> List.fold_left merge_bindings postbindings
     in
     let exec_implicits = fv_stmts exec in
     let exec_arg_needed id ty = IdentSet.mem id exec_implicits in
     let exec_args =
       Bindings.filter exec_arg_needed bindings
       |> Bindings.bindings
       |> List.map (fun (id, ty) -> (ty, id))
     in
     (* Bind expressions involving global type variable VL *)
     let exec = rewrite_pl exec in
     let vl_bindings = vl_exprs_of_stmts true exec in
     let vl_args = List.map (fun (_, id, _, _) -> (ASL_TC.type_integer, id)) vl_bindings in
     let vl_exprs = List.map (fun (_, _, expr, _) -> expr) vl_bindings in
     let vl_ncs = List.map (fun (_, _, _, nc) -> nc) vl_bindings in
     let add_binding ctx (key, id, _, _) =
       { ctx with bound_exprs = ExprMap.add key id ctx.bound_exprs }
     in
     let exec_ctx = List.fold_left add_binding ctx vl_bindings in
     let ics =
       let ics_of_encoding = function
         | Encoding_Block (_, _, _, _, _, _, stmts, _) ->
           let stmts = match opost with
             | Some ostmts -> stmts @ ostmts
             | None -> stmts
           in
           (* Run through the assignments in the decode twice to infer
              constraints on variables; the second run allows us to pick
              up assignments of values that depend on previously constrained
              variables. *)
           let ics = int_constraints_of_stmts stmts in
           let ics = int_constraints_of_stmts ~known_vars:ics stmts in
           Bindings.filter exec_arg_needed ics
           (* Usually we would only use constraints for variables that are
              guaranteed to be initialised, but ASL decode clauses have the tendency
              to not initialise variables that (due to the setting of other variables)
              will not be used in the execute clause. *)
           (* |> Bindings.filter (fun v _ -> IdentSet.mem v (initialised_vars stmts)) *)
       in
       let ics = List.map ics_of_encoding encodings in
       (* Merge constraints (restricting to variables declared in all encodings) *)
       let merge _ ic1 ic2 = match (ic1, ic2) with
         | (Some ic1, Some ic2) -> Some (merge_int_constraint ic1 ic2)
         | (_, _) -> None
       in
       match ics with
       | ics1 :: rest -> List.fold_left (Bindings.merge merge) ics1 rest
       | [] -> Bindings.empty
     in
     (* Check for potentially uninitialised variables *)
     let initialise_vars stmts =
       let is_uninitialised var _ =
         Bindings.mem var (locals_of_stmts stmts)
         && not (IdentSet.mem var (initialised_vars stmts))
       in
       let ics = Bindings.filter is_uninitialised ics in
       if Bindings.is_empty ics then stmts else begin
         let vars = List.map (fun (v, _) -> pprint_ident v) (Bindings.bindings ics) in
         print_endline ("Warning: Initialising variable(s) " ^ String.concat ", " vars);
         initialise_vars ics stmts
       end
     in
     let opost = Util.option_map initialise_vars opost in
     let encodings =
       let initialise_vars_enc (Encoding_Block (id, iset, fs, opc, g, unpreds, stmts, l)) =
         Encoding_Block (id, iset, fs, opc, g, unpreds, initialise_vars stmts, l)
       in
       List.map initialise_vars_enc encodings
     in
     let constraints =
       let add_constraint id ic ncs =
         match nc_of_int_constraint id ic with
         | Some nc -> nc :: ncs
         | None -> ncs
       in
       match Bindings.fold add_constraint ics vl_ncs with
         | [] -> []
         | ncs -> [List.fold_left nc_and nc_true ncs]
     in
     let exec_id = add_name_prefix "execute" id in
     sail_valspec_of_decl ~ncs:constraints exec_ctx exec_id unit_ty (vl_args @ exec_args) @
     sail_fundef_of_decl exec_ctx exec_id unit_ty (vl_args @ exec_args) exec @
     List.concat (List.map (sail_of_encoding ctx opost exec_id vl_exprs exec_args conditional) encodings)
  | Decl_NewMapDefn (_, _, _, _, _)
  | Decl_MapClause (_, _, _, _, _)
  | Decl_NewEventDefn (_, _, _)
  | Decl_EventClause (_, _, _) ->
     (* Handled separately below *)
     []
  | Decl_Operator1 (op, ids, _) ->
     [DEF_overload (sailify_unop op, List.map sail_id_of_ident ids)]
  | Decl_Operator2 (op, ids, _) ->
     [DEF_overload (sailify_binop op, List.map sail_id_of_ident ids)]
  | Decl_DecoderDefn (_, _, _) ->
     print_endline "TODO: Decl_DecoderDefn";
     []
  | Decl_BuiltinType (_, _)
  | Decl_Forward (_, _) -> []

let sail_of_maps ctx (decls: ASL_AST.declaration list) =
  let add_mapdef mapdefs = function
    | Decl_NewMapDefn (ret_ty, name, args, fallthrough, l) ->
       ASL_Utils.Bindings.add name (ret_ty, args, [], fallthrough, l) mapdefs
    | _ -> mapdefs
  in
  let mapdefs = List.fold_left add_mapdef ASL_Utils.Bindings.empty decls in
  let add_mapclause mapdefs = function
    | Decl_MapClause (name, fields, guard, body, l) ->
       let (ret_ty, args, clauses, fallthrough, l) =
         match ASL_Utils.Bindings.find_opt name mapdefs with
         | Some mapdef -> mapdef
         | None ->
            let name' = ASL_AST.pprint_ident name in
            failwith ("sail_of_maps: Clause for undefined map " ^ name')
       in
       let has_field_id id (MapField_Field (id', pat)) = (ASL_AST.Id.compare id id' = 0) in
       let get_arg_pat (ty, id) =
         match List.find_opt (has_field_id id) fields with
         | Some (MapField_Field (_, pat)) -> sail_of_pat ctx pat
         | None -> (mk_pat (P_id (sail_id_of_ident id)), None)
       in
       let guard' = Util.option_map (sail_of_expr ctx) guard in
       let (pat', guards') =
         match args with
         | [] -> (mk_pat P_wild, guard')
         | [arg] ->
            let (pat', pguard') = get_arg_pat arg in
            (pat', combine_guards "&" pguard' guard')
         | _ ->
            let (pats, pguards) = List.split (List.map get_arg_pat args) in
            let pguard = List.fold_right (combine_guards "&") pguards guard' in
            (mk_pat (P_tup pats), pguard)
       in
       let body' = sail_of_stmts ctx body in
       let clause = construct_pexp (pat', guards') body' in
       let mapdef' = (ret_ty, args, clause :: clauses, fallthrough, l) in
       ASL_Utils.Bindings.add name mapdef' mapdefs
    | _ -> mapdefs
  in
  let mapdefs' = List.fold_left add_mapclause mapdefs decls in
  let sail_of_mapdef (name, (ret_ty, args, clauses, fallthrough, l)) =
    let name' = sail_id_of_ident name in
    let fallthrough' = sail_of_stmts ctx fallthrough in
    let arg_pat (_, id) = mk_pat (P_id (sail_id_of_ident id)) in
    let arg_pats = match args with
      | [] -> mk_pat (P_lit (mk_lit L_unit))
      | [arg] -> arg_pat arg
      | args -> mk_pat (P_tup (List.map arg_pat args))
    in
    let fallthrough_cl = mk_pexp (Pat_exp (arg_pats, fallthrough')) in
    let clauses' = List.rev (fallthrough_cl :: clauses) in
    let mk_funcl cl = FCL_aux (FCL_Funcl (name', cl), no_annot) in
    mk_fundef (List.map mk_funcl clauses')
  in
  List.map sail_of_mapdef (ASL_Utils.Bindings.bindings mapdefs')

let sail_of_events ctx (decls: ASL_AST.declaration list) =
  let add_event evs = function
    | Decl_NewEventDefn (id, args, l) ->
       ASL_Utils.Bindings.add id (args, []) evs
    | Decl_EventClause (id, stmts', l) ->
       let (args, stmts) =
         match ASL_Utils.Bindings.find_opt id evs with
         | Some ev -> ev
         | None ->
            begin match get_asl_funtype id with
            | Some (_, _, _, _, args, _) -> (args, [])
            | _ -> ([], [])
            end
       in
       ASL_Utils.Bindings.add id (args, stmts @ stmts') evs
    | _ -> evs
  in
  let evs = List.fold_left add_event ASL_Utils.Bindings.empty decls in
  let sail_of_event (id, (args, stmts)) = sail_fundef_of_decl ctx id unit_ty args stmts in
  List.concat (List.map sail_of_event (ASL_Utils.Bindings.bindings evs))
