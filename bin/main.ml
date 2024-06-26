open LibASL.Asl_ast
open Libsail.Ast_util
open Libsail.Ast_defs
open Libsail.Type_error

module Sail_PP = Libsail.Pretty_print_sail
module Type_check = Libsail.Type_check
module Initial_check = Libsail.Initial_check
module Preprocess = Libsail.Preprocess
module Constraint = Libsail.Constraint
module Ast = Libsail.Ast
module Ast_defs = Libsail.Ast_defs
module Util = Libsail.Util
module Parse_ast = Libsail.Parse_ast
module Reporting = Libsail.Reporting
module Graph = Libsail.Graph
module Callgraph = Libsail.Callgraph
module ASL_AST = LibASL.Asl_ast
module ASL_Utils = LibASL.Asl_utils
module ASL_TC = LibASL.Tcheck
module ASL_PP = LibASL.Asl_parser_pp
module SS = Set.Make(String)
module Translate_asl = Asl_to_sail.Translate_asl
module Sail_to_sail = Asl_to_sail.Sail_to_sail

let time (s : string) (f : 'a -> 'b) (x : 'a) : 'b =
  let t = Sys.time() in
  let fx = f x in
  Printf.eprintf "(* %s time: %fs *)\n\n%!" s (Sys.time() -. t);
  fx

(* Command line flags *)

let input_files = ref ([] : string list)
let sail_lib_dir = ref ("" : string)
let output_dir = ref (None : string option)
let patch_dir = ref "patches"
let write_osails = ref false
let interactive = ref true
let quiet = ref false
let overrides = ref ([] : (string * string) list)
let slice_roots = ref ([] : string list)
let slice_cuts = ref ([] : string list)
let gen_stubs = ref false
let stop_at = ref ([] : string list)

let read_overrides_file filename =
  let file = open_in filename in
  let rec read_lines () =
    match input_line file with
    | l ->
       begin match String.split_on_char ' ' l with
         | [fun_id; fun_file] ->
            overrides := !overrides @ [(fun_id, Filename.basename fun_file)]
         | [] -> ()
         | _ -> failwith ("Failed to parse override in line " ^ l)
       end;
       read_lines ()
    | exception End_of_file -> ()
  in
  read_lines ();
  close_in file

let options = Arg.align ([
  ( "-sail_lib_dir",
    Arg.String (fun s -> sail_lib_dir := s),
    " location of the Sail library directory");
  ( "-outdir",
    Arg.String (fun s -> output_dir := Some s),
    " set the output directory");
  ( "-patches",
    Arg.String (fun l -> patch_dir := l),
    " set the directory containing patch files");
  ( "-overrides",
    Arg.String (fun f -> read_overrides_file f),
    " read function overrides from file");
  ( "-osails",
    Arg.Set write_osails,
    " write generated Sail files before type-checking to patch directory");
  ( "-non_interactive",
    Arg.Clear interactive,
    " run in non interactive mode");
  ( "-quiet",
    Arg.Set quiet,
    " suppress progress output");
  ( "-mono_vl",
    Arg.Set Translate_asl.mono_vl,
    " enable monomorphisation of VL in decode clauses");
  ( "-bind_vl_ariths",
    Arg.Set Translate_asl.bind_vl_ariths,
    " pull arithmetic expressions involving vector lengths out into parameters of functions");
  ( "-implemented_vls",
    Arg.String (fun l -> Translate_asl.implemented_vls := List.map int_of_string (String.split_on_char ',' l)),
    " set supported values of VL");
  ( "-mono_splits_file",
    Arg.String (fun f -> Translate_asl.read_mono_splits_file f),
    " read additional monomorphisation splits from file");
  ( "-no_see_checks",
    Arg.Clear Translate_asl.opt_see_checks,
    " omit SEE checks and updates in decoder");
  ( "-slice_roots",
    Arg.String (fun l -> slice_roots := !slice_roots @ (String.split_on_char ',' l)),
    " slice specification to given (comma-separated list of) functions and their dependencies");
  ( "-slice_cuts",
    Arg.String (fun l -> slice_cuts := !slice_cuts @ (String.split_on_char ',' l)),
    " remove given (comma-separated list of) functions when slicing");
  ( "-gen_stubs",
    Arg.Set gen_stubs,
    " generate stubs for missing functions and output to stubs.sail");
  ( "-stop_at",
    Arg.String (fun l -> stop_at := !stop_at @ (String.split_on_char ',' l)),
    " stop at functions in the given comma-separated list and allow patching");
])

let ident_loc_of_decl (decl : declaration) : (ident * l) =
  match decl with
  | Decl_BuiltinType (id, l)
  | Decl_Forward (id, l)
  | Decl_Record (id, _, l)
  | Decl_Typedef (id, _, l)
  | Decl_Enum (id, _, l)
  | Decl_Var (_, id, l)
  | Decl_Const (_, id, _, l)
  | Decl_BuiltinFunction (_, id, _, l)
  | Decl_FunType (_, id, _, l)
  | Decl_FunDefn (_, id, _, _, l)
  | Decl_ProcType (id, _, l)
  | Decl_ProcDefn (id, _, _, l)
  | Decl_VarGetterType (_, id, l)
  | Decl_VarGetterDefn (_, id, _, l)
  | Decl_ArrayGetterType (_, id, _, l)
  | Decl_ArrayGetterDefn (_, id, _, _, l)
  | Decl_VarSetterType (id, _, _, l)
  | Decl_VarSetterDefn (id, _, _, _, l)
  | Decl_ArraySetterType (id, _, _, _, l)
  | Decl_ArraySetterDefn (id, _, _, _, _, l)
  | Decl_InstructionDefn (id, _, _, _, _, l)
  | Decl_DecoderDefn (id, _, l)
  | Decl_NewEventDefn (id, _, l)
  | Decl_EventClause (id, _, l)
  | Decl_NewMapDefn (_, id, _, _, l)
  | Decl_MapClause (id, _, _, _, l)
  | Decl_Config (_, id, _, l) -> (id, l)
  | Decl_Operator1 (_, _, _) -> failwith "ident_of_decl: Decl_Operator1"
  | Decl_Operator2 (_, _, _) -> failwith "ident_of_decl: Decl_Operator2"

let ident_of_decl decl = fst (ident_loc_of_decl decl)
let loc_of_decl decl = snd (ident_loc_of_decl decl)

let name_of_ident = function
  | Ident name
  | FIdent (name, _) -> name

let defined_idents (decl : declaration) : ASL_Utils.IdentSet.t =
  let extra_ids =
    match decl with
    | Decl_Enum (_, ids, _) -> ASL_Utils.IdentSet.of_list ids
    | _ -> ASL_Utils.IdentSet.empty
  in
  ASL_Utils.IdentSet.add (ident_of_decl decl) extra_ids

let is_operator_decl = function
  | Decl_Operator1 (_, _, _)
  | Decl_Operator2 (_, _, _) -> true
  | _ -> false

let is_val_decl = function
  | Decl_BuiltinFunction (_, _, _, _)
  | Decl_FunType (_, _, _, _)
  | Decl_ProcType (_, _, _)
  | Decl_VarGetterType (_, _, _)
  | Decl_ArrayGetterType (_, _, _, _)
  | Decl_VarSetterType (_, _, _, _)
  | Decl_ArraySetterType (_, _, _, _, _) -> true
  | _ -> false

let is_fun_decl = function
  | Decl_BuiltinFunction _
  | Decl_FunDefn _
  | Decl_ProcDefn _
  | Decl_VarGetterDefn _
  | Decl_VarSetterDefn _
  | Decl_ArrayGetterDefn _
  | Decl_ArraySetterDefn _ -> true
  | _ -> false

let is_map_decl = function
  | Decl_NewMapDefn _ -> true
  | _ -> false

let is_event_decl = function
  | Decl_NewEventDefn _ -> true
  | _ -> false

let is_clause_decl = function
  | Decl_EventClause (_, _, _) -> true
  | Decl_MapClause (_, _, _, _, _) -> true
  | _ -> false

let is_var_decl = function
  | Decl_Var (_, _, _)
  | Decl_Config (_, _, _, _) -> true
  | _ -> false

let is_const_decl = function
  | Decl_Const (_, _, _, _) -> true
  | _ -> false

let is_type_decl = function
  | Decl_BuiltinType (_, _)
  | Decl_Record (_, _, _)
  | Decl_Typedef (_, _, _)
  | Decl_Enum (_, _, _) -> true
  | _ -> false

let is_sail_builtin_decl decl =
  let open Translate_asl in
  StringSet.mem (name_of_ident (ident_of_decl decl)) builtins

let print_decl decl =
  PPrint.ToChannel.pretty 1. 80 stdout (ASL_PP.pp_declaration decl)

let string_of_decl decl = LibASL.Utils.to_string (ASL_PP.pp_declaration decl)

let string_of_encoding (Encoding_Block (id, iset, fs, opc, g, unpreds, stmts, l)) =
  let enc = Encoding_Block (stripTag id, iset, fs, opc, g, unpreds, stmts, l) in
  LibASL.Utils.to_string (ASL_PP.pp_encoding enc)

class enumsClass = object
    inherit LibASL.Asl_visitor.nopAslVisitor

    val mutable es = ASL_Utils.IdentSet.empty
    method result = es
    method! vpattern = function
      | Pat_Const id ->
         es <- ASL_Utils.IdentSet.add id es;
         DoChildren
      | _ -> DoChildren
    method! vtype = function
      | Type_Array (Index_Enum id, _) ->
         es <- ASL_Utils.IdentSet.add id es;
         DoChildren
      | _ -> DoChildren
end

let enums_of_decl decl =
  let open LibASL.Asl_visitor in
  let es = new enumsClass in
  ignore (visit_decl (es :> aslVisitor) decl);
  es#result

class impdefTypesClass = object
    inherit LibASL.Asl_visitor.nopAslVisitor

    val mutable ids = ASL_Utils.IdentSet.empty
    method result = ids
    method! vexpr = function
      | Expr_ImpDef (Type_Constructor id, _) ->
         ids <- ASL_Utils.IdentSet.add id ids;
         DoChildren
      | Expr_ImpDef (Type_Bits _, _) ->
         ids <- ASL_Utils.IdentSet.add (Ident "bits") ids;
         DoChildren
      | _ -> DoChildren
end

let impdef_types_of_decl decl =
  let open LibASL.Asl_visitor in
  let ids = new impdefTypesClass in
  ignore (visit_decl (ids :> aslVisitor) decl);
  ids#result

let impdef_types_of_decls decls =
  ASL_Utils.unionSets (List.map impdef_types_of_decl decls)

let impdef_of_type id = Ident ("__IMPDEF_" ^ name_of_ident id)

let impdef_decl id =
  let ty = Type_Constructor id in
  let fun_id = impdef_of_type id in
  let arg = (ASL_TC.type_string, Ident "x") in
  let decl = Decl_FunType (ty, fun_id, [arg], Unknown) in
  let body = Stmt_FunReturn (Expr_Unknown ty, Unknown) in
  let impl = Decl_FunDefn (ty, fun_id, [arg], [body], Unknown) in
  [decl; impl]

type sail_ast = untyped_ast

let header = ref (None : string option)

let get_header () =
  match !header with
  | None -> begin
     try
       let in_chan = open_in (!patch_dir ^ "/HEADER") in
       let contents = ref "" in
       begin try
         while true do
           let line = input_line in_chan in
           contents := !contents ^ line ^ "\n"
         done;
         ""
       with
       | End_of_file ->
          close_in in_chan;
          header := Some !contents;
          !contents
       end
     with
     | _ ->
        print_endline ("Warning: Could not load " ^ !patch_dir ^ "/HEADER");
        header := Some "";
        ""
     end
  | Some contents -> contents

(*Pretty print sail to a file*)
let write_sail (sail_ast : sail_ast) (filename : string) : unit =
  let (temp_filename, o) = Filename.open_temp_file (Filename.basename filename) "_temp.sail" in
  begin
    output_string o (get_header ());
    Sail_PP.output_ast o sail_ast;
    close_out o;
    Util.move_file temp_filename filename;
  end

let termcode n = "\x1B[" ^ string_of_int n ^ "m"

let bold str = termcode 1 ^ termcode 33 ^ str ^ termcode 0
let emph str = termcode 1 ^ termcode 35 ^ str ^ termcode 0
let green str = termcode 1 ^ termcode 32 ^ str ^ termcode 0
(* let red str = termcode 1 ^ termcode 31 ^ str ^ termcode 0 *)

let is_valspec = function
  | Ast.DEF_aux (Ast.DEF_val _, _) -> true
  | Ast.DEF_aux (Ast.DEF_overload _, _) -> true
  | _ -> false

let get_editor =
  try Sys.getenv "VISUAL" with
  | Not_found ->
  try Sys.getenv "EDITOR" with
  | Not_found -> print_endline "EDITOR and VISUAL environment vars unset"; "vim"

exception Asl_type_error of untyped_ast * Parse_ast.l * string;;

module StringSet = Set.Make(String)
module StringMap = Map.Make(String)
module StringGraph = Graph.Make(String)

(* The ASL code is split up into 'chunks' that we translate into
   sail. Some of these chunks are in turn subdivided into a val chunk
   and a body chunk, which means turn this ASL into the valspec and
   the body of a function respectively. *)
let done_chunks = ref 0
let num_chunks = ref 0

type chunk =
  | Chunk_vals of declaration list
  | Chunk_decls of declaration list

let chunk_decls = function
  | Chunk_vals decls
  | Chunk_decls decls -> decls

let is_val_chunk = function
  | Chunk_vals _ -> true
  | Chunk_decls _ -> false

let is_empty_chunk chunk = (chunk_decls chunk = [])

let chunk_name_of_decl decl =
  name_of_ident (stripTag (ident_of_decl decl))

let name_of_chunk chunk =
  match chunk_decls chunk with
  | decl :: _ -> chunk_name_of_decl decl
  | _ -> failwith "chunk_name: Empty chunk"

let add_decl_to_chunk ?previous_chunks:(pc=StringMap.empty) chunk decl =
  (* Check for duplicate val decls, which the ASL typechecker tends to
     produce. *)
  let id = ident_of_decl decl in
  let previous_decls = if StringMap.mem (chunk_name_of_decl decl) pc then chunk_decls (StringMap.find (chunk_name_of_decl decl) pc) else [] in
  let decls = previous_decls @ chunk_decls chunk in
  let is_duplicate decl' =
    (is_val_decl decl = is_val_decl decl')
    && (is_map_decl decl = is_map_decl decl')
    && (is_event_decl decl = is_event_decl decl')
    && (not (is_clause_decl decl'))
    && (is_type_decl decl = is_type_decl decl')
    && ASL_AST.Id.compare (ident_of_decl decl') id == 0
  in
  let has_conflict decl' = is_duplicate decl' && (string_of_decl decl <> string_of_decl decl') in
  let pp_conflict decl' = " * At " ^ pp_loc (loc_of_decl decl') ^ ": " ^ string_of_decl decl' in
  if (List.exists has_conflict decls) then begin
      prerr_endline "Conflicting declarations:";
      List.iter print_endline (List.map pp_conflict (List.filter has_conflict decls @ [decl]));
      failwith "Conflicting declarations"
    end else
  if (List.exists is_duplicate decls) then chunk else
  match chunk with
  | Chunk_vals decls ->
     if is_val_decl decl then Chunk_vals (decls @ [decl]) else
     Chunk_decls (decls @ [decl])
  | Chunk_decls decls -> Chunk_decls (decls @ [decl])

let merge_chunks c1 c2 = List.fold_left add_decl_to_chunk c1 (chunk_decls c2)

let empty_chunk = Chunk_vals []

let singleton_chunk decl = add_decl_to_chunk empty_chunk decl

let chunk_map_of_decls ?previous_chunks:(pc=StringMap.empty) decls =
  let add bindings decl =
    let name = chunk_name_of_decl decl in
    let chunk =
      try StringMap.find name bindings with
      | Not_found -> empty_chunk
    in
    StringMap.add name (add_decl_to_chunk ~previous_chunks:pc chunk decl) bindings
  in
  List.fold_left add StringMap.empty decls

let graph_of_decls decls =
  let add graph decl =
    let open ASL_Utils in
    let is_global id = (ASL_TC.GlobalEnv.getGlobalVar ASL_TC.env0 id <> None) in
    let uses =
      IdentSet.union (fv_decl decl) (assigned_vars_of_decl decl)
      |> IdentSet.filter is_global
      |> IdentSet.union (types_of_decl decl)
      |> IdentSet.union (calls_of_decl decl)
      |> IdentSet.union (enums_of_decl decl)
      |> IdentSet.union (IdentSet.map impdef_of_type (impdef_types_of_decl decl))
      |> IdentSet.elements
      |> List.map name_of_ident
    in
    let defines =
      IdentSet.elements (defined_idents decl)
      |> List.map name_of_ident
    in
    let name = ident_of_decl decl |> name_of_ident in
    StringGraph.add_edges name uses graph
    |> List.fold_right (fun name' g -> StringGraph.add_edge name' name g) defines
  in
  List.fold_left add StringGraph.empty decls

let get_chunks ?previous_chunks:(pc=StringMap.empty) decls =
  let chunk_map = chunk_map_of_decls ~previous_chunks:pc decls in
  let names = List.map ident_of_decl decls |> List.map name_of_ident in
  let components = StringGraph.scc ~original_order:names (graph_of_decls decls) in
  let chunks_of_component component =
    let get_chunk name =
      try StringMap.find name chunk_map with
      | Not_found -> empty_chunk
    in
    let chunk =
      List.map get_chunk component
      |> List.fold_left merge_chunks empty_chunk
    in
    match component with
    | [] -> failwith ("Empty dependency graph component")
    | [_] -> [chunk]
    | _ ->
       (* Mutually recursive declarations; partition into
          type-defs, val-specs, then definitions *)
       let (type_decls, decls) = List.partition is_type_decl (chunk_decls chunk) in
       let (const_decls, decls) = List.partition is_const_decl decls in
       let (var_decls, decls) = List.partition is_var_decl decls in
       let (val_decls, decls) = List.partition is_val_decl decls in
       List.map singleton_chunk (type_decls @ const_decls @ var_decls @ val_decls @ decls)
  in
  List.concat (List.map chunks_of_component components)
  |> List.filter (fun c -> not (is_empty_chunk c))

let rec merge_encodings = function
  | (Decl_InstructionDefn (id, _, _, _, _, _) as decl) :: decls ->
     (* Check for other instructions with same identifier and execute clause and
        merge encodings *)
     let pp_stmts = List.map ASL_Utils.pp_stmt in
     let stmts_eq s1 s2 = pp_stmts s1 = pp_stmts s2 in
     let ostmts_eq s1 s2 = stmts_eq (Option.value ~default:[] s1) (Option.value ~default:[] s2) in
     let merge i1 i2 = match (i1, i2) with
       | (Decl_InstructionDefn (id1, encs1, opost1, cond1, exec1, l1),
          Decl_InstructionDefn (id2, encs2, opost2, cond2, exec2, _))
         when ASL_AST.Id.compare id1 id2 = 0 && ostmts_eq opost1 opost2 && cond1 = cond2
           && stmts_eq exec1 exec2 ->
          Decl_InstructionDefn (id1, encs1 @ encs2, opost1, cond1, exec1, l1)
       | (decl1, decl2) ->
          print_endline ("Conflicting instruction definitions " ^ pprint_ident id ^ " at");
          print_endline (pp_loc (loc_of_decl decl1));
          print_endline (pp_loc (loc_of_decl decl2));
          failwith "Conflicts"
     in
     let has_id decl' = ASL_AST.Id.compare id (ident_of_decl decl') = 0 in
     let (to_merge, rest) = List.partition has_id decls in
     let decl' = List.fold_left merge decl to_merge in
     (* Check that all encodings have different identifiers *)
     let decl'' = match decl' with
       | Decl_InstructionDefn (id, encs, opost, cond, exec, l) ->
          let add encs (Encoding_Block (id, iset, fs, opc, g, unpreds, stmts, l) as enc) =
            let is_duplicate enc' = string_of_encoding enc = string_of_encoding enc' in
            if List.exists is_duplicate encs then encs else begin
              let has_id (Encoding_Block (id', _, _, _, _, _, _, _)) =
                name_of_ident id = name_of_ident id'
              in
              let same_ids = List.filter has_id encs in
              let id = addTag id (List.length same_ids) in
              encs @ [Encoding_Block (id, iset, fs, opc, g, unpreds, stmts, l)]
            end
          in
          let encs = List.fold_left add [] encs in
          Decl_InstructionDefn (id, encs, opost, cond, exec, l)
       | decl -> decl
     in
     decl'' :: merge_encodings rest
  | decl :: decls -> decl :: merge_encodings decls
  | [] -> []

let patch_file is_forward chunk =
  let ext = if is_forward then ".val.sail" else ".sail" in
  !patch_dir ^ "/" ^ name_of_chunk chunk ^ ext

let orig_file is_forward chunk =
  let ext = if is_forward then ".val.osail" else ".osail" in
  !patch_dir ^ "/" ^ name_of_chunk chunk ^ ext

let rec get_unresolved_quants (err: type_error) =
  let open Type_check in
  match err with
  | Err_unresolved_quants (_, quants, locals, tyvars, ncs) -> [(quants, locals, tyvars, ncs)]
  | Err_failed_constraint (check, locals, tyvars, ncs)
  | Err_inner (Err_failed_constraint (check, locals, tyvars, ncs), _, _, _) ->
     [([mk_qi_nc check], locals, tyvars, ncs)]
  | Err_no_overloading (_, errs') ->
     List.concat (List.map (fun (_, _, err) -> get_unresolved_quants err) errs')
  | Err_inner (err1, _, _, err2) ->
     get_unresolved_quants err1 @ get_unresolved_quants err2
  | Err_subtype (typ1, typ2, _, ncs, tyvars) ->
     begin match destruct_numeric typ1, destruct_numeric typ2 with
       | Some ([], nc1, nexp1), Some ([], nc2, nexp2) ->
          let nc = nc_and (nc_eq nexp1 nexp2) (nc_and nc1 nc2) in
          [([mk_qi_nc nc], Bindings.empty, tyvars, List.map snd ncs)]
       | _ -> []
     end
  | Err_instantiation_info (_, err)
  | Err_function_arg (_, _, err)
  | Err_with_hint (_, err) -> get_unresolved_quants err
  | Err_no_num_ident _
  | Err_not_in_scope _
  | Err_no_function_type _
  | Err_unbound_id _
  | Err_hint _
  | Err_other _ -> []

let is_duplicate_def (err: type_error) (Ast.DEF_aux (def, _)) =
  let open Ast in
  let err_str, _ = string_of_type_error err in
  let is_err str = Str.string_match (Str.regexp_string str) err_str 0 in
  match def with
  | DEF_register (DEC_aux (DEC_reg (_, id, _), _)) ->
     is_err ("Register " ^ string_of_id id ^ " is already bound")
  | DEF_fundef fd ->
     is_err ("Function " ^ string_of_id (id_of_fundef fd) ^ " has already been declared")
  | DEF_type (TD_aux (TD_enum (id, _, _), _)) ->
     is_err ("Cannot create enum " ^ string_of_id id ^ ", type name is already bound")
  | DEF_type (TD_aux (TD_record (id, _, _, _), _)) ->
     is_err ("Cannot create record " ^ string_of_id id ^ ", type name is already bound")
  | DEF_type (TD_aux (TD_abbrev (id, _, _), _)) ->
     is_err ("Type synonym " ^ string_of_id id ^ " already exists")
  | _ -> false

let rec remove_first pred = function
  | x :: xs when pred x -> xs
  | x :: xs -> x :: remove_first pred xs
  | [] -> []

let remove_duplicate_def err decls =
  List.rev (remove_first (is_duplicate_def err) (List.rev decls))

let is_duplicate_val_spec (ctx : Translate_asl.ctx) = function
  | Ast.DEF_aux (Ast.DEF_val (Ast.VS_aux (Ast.VS_val_spec (_, id, _), _)), _) ->
     Translate_asl.is_sail_fun_declared ctx.tc_env id
  | _ -> false

let get_fundef_id = function
  | Ast.DEF_aux (Ast.DEF_fundef fd, _) -> [id_of_fundef fd]
  | _ -> []

let report_sail_error (ctx: Translate_asl.ctx) decls sail convert continue =
  try convert ()
  with
  | Asl_type_error (sail, l, e) ->
     print_endline (bold "\nConverting ASL:");
     List.iter print_decl decls;
     print_endline (bold "\nFailed to typecheck the following sail:");
     Sail_PP.output_ast stdout sail;
     print_endline (bold "\nDerivation:");
     Type_check.set_tc_debug 1;
     let _, _ =
       try check ctx.tc_env sail with
       | Reporting.Fatal_error _ -> empty_ast, ctx.tc_env
     in
     Type_check.set_tc_debug 0;
     print_endline (bold "\nReason:");
     print_endline (Reporting.loc_to_string l);
     print_endline e;
     continue ()
  | Reporting.Fatal_error e ->
     print_endline (bold "Sail fatal error when processing:");
     Sail_PP.output_ast stdout sail;
     Reporting.print_error e;
     exit 1

let quant_error_eq (quants1, _, _) (quants2, _, _) =
  String.concat ", " (List.map string_of_quant_item quants1)
  = String.concat ", " (List.map string_of_quant_item quants2)

let constraints_with_kopts kopts ncs =
  List.filter (fun nc -> not (KOptSet.disjoint (kopts_of_constraint nc) kopts)) ncs

let merge_quant_errs global_env ((quants1, locals1, tyvars1, ncs1) as err1) ((quants2, locals2, tyvars2, ncs2) as err2) =
  let open Type_check in
  let open Sail_to_sail in
  (* Bail out if the environments are different *)
  let quant_kopts1 = kopts_of_quant_items quants1 in
  let quant_tyvars1 = filter_type_variables quant_kopts1 tyvars1 in
  let quant_ncs1 = constraints_with_kopts quant_kopts1 ncs1 in
  let quant_kopts2 = kopts_of_quant_items quants2 in
  let quant_tyvars2 = filter_type_variables quant_kopts2 tyvars2 in
  let quant_ncs2 = constraints_with_kopts quant_kopts2 ncs2 in
  if Bindings.compare compare_local locals1 locals2 <> 0 then None else
  if compare_type_variables quant_tyvars1 quant_tyvars2 <> 0 then None else
  if List.compare NC.compare quant_ncs1 quant_ncs2 <> 0 then None else
  (* If the errors are equal, return one of them *)
  if List.compare QuantItem.compare quants1 quants2 = 0 then Some err1 else
  (* Otherwise, check if the unresolved constraints of one imply those of the other *)
  let env = mk_local_env tyvars1 ncs1 global_env in
  let qi_constraints = function
    | Ast.QI_aux (Ast.QI_constraint nc, _) -> [nc]
    | _ -> []
  in
  let qis_constraint qis =
    List.concat (List.map qi_constraints qis)
    |> List.fold_left nc_and nc_true
  in
  let implies nc1 nc2 =
    try prove __POS__ (Env.add_constraint nc1 env) nc2 with
    | _ -> false
  in
  let nc1 = qis_constraint quants1 in
  let nc2 = qis_constraint quants2 in
  if implies nc1 nc2 then Some err1 else
  if implies nc2 nc1 then Some err2 else
  None

let merge_quant_errs_opt env oerr1 err2 =
  match oerr1 with
  | Some err1 -> merge_quant_errs env err1 err2
  | None -> None

let merge_unresolved_quants env err =
  match get_unresolved_quants err with
  | err :: errs -> List.fold_left (merge_quant_errs_opt env) (Some err) errs
  | [] -> None

let is_sail_filename n = (String.sub n (String.length n - 5) 5 = ".sail")
let is_asl_filename n = (String.sub n (String.length n - 4) 4 = ".asl")
let asl_basename n = String.sub n 0 (String.length n - 4)
let sail_filename base = match !output_dir with
  | None -> base ^ ".sail"
  | Some dir ->
     let base = Filename.basename base in
     Filename.concat dir (base ^ ".sail")

(* Library files contain a few $option directives that it's safe for us to
   ignore at this stage. *)
let ignored_options = [
  ("-lem_extern_type", Arg.String (fun _ -> ()), "");
  ("-coq_extern_type", Arg.String (fun _ -> ()), "");
]

let parse_sail_file filename =
  let parsed_ast = Libsail.Initial_check.parse_file filename |> snd in
  let parsed_ast = Libsail.Preprocess.preprocess !sail_lib_dir None ignored_options parsed_ast in
  let ast = Libsail.Initial_check.process_ast ~generate:false (Libsail.Parse_ast.Defs [(filename, parsed_ast)]) in
  let vs_ids = val_spec_ids ast.defs in
  { ast with defs = ast.defs |> Initial_check.generate_undefineds vs_ids |> Initial_check.generate_enum_functions vs_ids }

let rec interact ?use_patches:(use_patches=true) ctx sail chunk rest =
  print_endline (green "\nWhat do you want to do?");
  print_endline ("(p) patch, (x) exit, (s) skip:");

  match input_line stdin with
  | "x" | "exit" -> Constraint.save_digests (); exit 1
  | "s" | "skip" -> convert_ast ~use_patches ctx rest
  | "p" | "patch" ->
     begin
       let is_val = is_val_chunk chunk in
       write_sail sail (patch_file is_val chunk);
       write_sail sail (orig_file is_val chunk);
       let cmd = get_editor ^ " " ^ patch_file is_val chunk in
       print_endline ("Executing: " ^ cmd);
       ignore (Sys.command cmd);
       convert_ast ~use_patches ctx (chunk :: rest)
     end
  | str ->
     begin
       print_endline ("Unrecognised command: " ^ str);
       interact ~use_patches ctx sail chunk rest
     end

and iterate_check ?(modify_val_specs=true) n env sail =
  let open Type_check in
  try
    let checked_sail, env = check env sail in
    checked_sail, sail, env
  with
  | Type_error (l, err) when n <= 50 ->
     begin match merge_unresolved_quants env err with
     | Some (quants, locals, tyvars, ncs) ->
        let local_env = Sail_to_sail.mk_local_env tyvars ncs env in
        let fix_quant sail quant =
          match analyze_unresolved_quant locals ncs quant with
          | Suggest_add_constraint nc
            when not (prove __POS__ local_env (nc_not nc)) ->
             begin
               try
                 Sail_to_sail.rewrite_add_constraint ~modify_val_spec:modify_val_specs l env nc tyvars ncs sail
               with
               | Type_error (_, err) ->
                  prerr_endline Util.(string_of_type_error err |> fst |> red |> clear);
                  sail
               | Failure msg ->
                  prerr_endline Util.(msg |> red |> clear);
                  sail
             end
          | _ ->
             prerr_endline "No suggestion";
             sail
        in
        let sail = List.fold_left fix_quant sail quants in
        iterate_check ~modify_val_specs (n + 1) env sail
     | None ->
        if List.exists (is_duplicate_def err) sail.defs then begin
          print_endline "Warning: Duplicate definitions!";
          let sail' = { sail with defs = remove_duplicate_def err sail.defs } in
          iterate_check ~modify_val_specs (n + 1) env sail'
        end else
          raise (Asl_type_error (sail, l, string_of_type_error err |> fst))
     end
  | Type_error (l, err) -> raise (Asl_type_error (sail, l, string_of_type_error err |> fst))

and convert_ast ?use_patches:(use_patches=true) ctx = function
  | [] -> empty_ast, empty_ast, ctx
  | (Chunk_vals [] :: rest) | (Chunk_decls [] :: rest) ->
     incr done_chunks;
     convert_ast ~use_patches ctx rest
  | (chunk :: rest) ->
     begin
       let (is_forward, decls) = (is_val_chunk chunk, chunk_decls chunk) in
       let has_patch = Sys.file_exists (patch_file is_forward chunk) in
       let has_val_spec_patch = Sys.file_exists (patch_file true chunk) in

       incr done_chunks;
       if is_forward then print_string (green "F ") else ();
       if not !quiet then print_endline (emph "Processing top" ^ " (" ^ string_of_int !done_chunks ^ "/" ^ string_of_int !num_chunks ^ "): " ^ name_of_chunk chunk);

       let sail =
         if use_patches && has_patch
         then
           let sail = concat_ast (List.map (Translate_asl.ast_of_declaration ctx) decls) in
           (* let sail = Sail_to_sail.rewrite_overloaded_top sail in *)
           let sail = Sail_to_sail.rewrite_mutated_parameters sail in
           write_sail sail (orig_file is_forward chunk);

           try
             let file = patch_file is_forward chunk in
             parse_sail_file file
           with
           | Reporting.Fatal_error e ->
              print_endline (bold "\nFailed to parse patch file: " ^ patch_file is_forward chunk);
              Reporting.print_error e;
              exit 1
         else if use_patches && has_val_spec_patch
         then
           (* Try loading val-specs from the patch file, but translate the remaining decls from ASL *)
           try
             let (val_decls, decls) = List.partition is_val_decl decls in
             let file = patch_file true chunk in
             let vals = parse_sail_file file in
             let check_vals () = Type_check.check ctx.tc_env vals in
             let (_, env) = report_sail_error ctx val_decls vals check_vals (fun _ -> exit 1) in
             let ctx = { ctx with tc_env = env } in
             let sail = concat_ast (vals :: (List.map (Translate_asl.ast_of_declaration ctx) decls)) in
             let sail = Sail_to_sail.rewrite_mutated_parameters sail in
             let sail = Sail_to_sail.eventually_constant sail in
             let sail = Sail_to_sail.vector_exps sail in
             sail
           with
           | Reporting.Fatal_error e ->
              print_endline (bold "\nFailed to parse patch file: " ^ patch_file true chunk);
              Reporting.print_error e;
              exit 1
           | Failure m ->
              print_endline (bold "Failed to generate sail from ASL:");
              List.iter print_decl decls;
              failwith m
         else
           try
             let sail = concat_ast (List.map (Translate_asl.ast_of_declaration ctx) decls) in
             let _ = if !write_osails then write_sail sail (orig_file is_forward chunk) in
             (* let sail = Sail_to_sail.rewrite_overloaded_top sail in *)
             let sail = Sail_to_sail.rewrite_mutated_parameters sail in
             let sail = Sail_to_sail.eventually_constant sail in
             let sail = Sail_to_sail.vector_exps sail in
             sail
           with
           | Failure m ->
              print_endline (bold "Failed to generate sail from ASL:");
              List.iter print_decl decls;
              failwith m
       in

       let sail = if is_forward then Sail_to_sail.filter_ast is_valspec sail else sail in
       let sail = Sail_to_sail.filter_ast (fun d -> not (is_duplicate_val_spec ctx d)) sail in

       report_sail_error ctx decls sail
         (fun _ ->
            let sail = Sail_to_sail.rewrite_make_unique sail in

            (* Type-check *)
            let modify_val_specs = not (has_patch || has_val_spec_patch) in
            let checked_sail, sail, env = iterate_check ~modify_val_specs 0 ctx.tc_env sail in

            let fun_ids = List.concat (List.map get_fundef_id checked_sail.defs) in

            (* The lexer/parser and initial check have side-effects we
              need for incremental typechecking so we have to write each
              top to a separate file and call the parser and throw away
              the result. Yes seriously... *)
            if sail.defs = [] then ()
            else begin
              write_sail sail (sail_filename "temp");
              ignore (Initial_check.parse_file (sail_filename "temp"))
            end;

            if List.exists (fun f -> List.mem (string_of_id f) !stop_at) fun_ids
            then raise (Asl_type_error (sail, Parse_ast.Unknown, "Asked to stop here"));

            (* Generate enum functions and add them to the environment.
               We might use them when translating enum-indexed arrays. *)
            let vals_in_env =
              Type_check.Env.get_val_specs ctx.tc_env
              |> Bindings.bindings |> List.map fst |> IdSet.of_list
            in
            let vals_in_defs = val_spec_ids (sail.defs) in
            let vals = IdSet.union vals_in_env vals_in_defs in
            let is_new_val = function
              | Ast.DEF_aux (DEF_val vs, _) -> not (IdSet.mem (id_of_val_spec vs) vals)
              | _ -> false
            in
            let _, env =
              Initial_check.generate_enum_functions vals sail.defs
              |> List.filter is_new_val
              |> Type_check.check_defs env
            in

            let ctx = { ctx with tc_env = env } in
            let (checked_sail', sail', ctx) = convert_ast ~use_patches ctx rest in
            (append_ast checked_sail checked_sail', append_ast sail sail', ctx))
         (fun _ ->
            if !interactive
            then interact ~use_patches ctx sail chunk rest
            else exit 1)
     end

type processed_file =
  | ASL_File of string * LibASL.Asl_ast.declaration list * Type_check.typed_ast * untyped_ast
  | Sail_File of string * Type_check.typed_ast

let write_processed_file = function
  | ASL_File (filename, _, _, ast) ->
     write_sail ast (sail_filename (asl_basename filename));
  | Sail_File _ -> ()

let sail_ast_of_processed_file = function
  | ASL_File (_, _, ast, _)
  | Sail_File (_, ast) -> ast

let asl_decls_of_processed_file = function
  | ASL_File (_, decls, _, _) -> decls
  | _ -> []

let load_asl is_prelude filename = LibASL.LoadASL.read_file filename is_prelude false

let process_asl_file ((ctx : Translate_asl.ctx), maps, events, clauses, previous_chunks, previous_files) filename =
  let decls = if !quiet then load_asl false filename else time ("Read ASL file " ^ filename) (load_asl false) filename in

  let impdef_decls =
    ASL_Utils.IdentSet.elements (impdef_types_of_decls decls)
    |> List.filter (fun id -> ASL_TC.GlobalEnv.getFuns ASL_TC.env0 (impdef_of_type id) = [])
    |> List.map impdef_decl |> List.concat
  in

  let bitfields =
    Translate_asl.bitfields_of_decls decls
    |> Libsail.Ast_util.Bindings.union (fun _ x _ -> Some x) ctx.bitfields
  in
  let ctx = { ctx with bitfields } in

  (* Filter out overridden functions that should be taken from other files *)
  let overriden_funs =
    List.filter (fun (_, f) -> f <> Filename.basename filename) !overrides
    |> List.map fst |> StringSet.of_list
  in
  let overridden decl =
    is_fun_decl decl && StringSet.mem (name_of_ident (ident_of_decl decl)) overriden_funs
  in
  let decls = List.filter (fun d -> not (overridden d)) decls in

  let (_builtins, decls) = List.partition is_sail_builtin_decl decls in
  let (op_decls, decls) = List.partition is_operator_decl decls in
  let (clauses', decls) = List.partition is_clause_decl decls in
  let (maps', decls) = List.partition is_map_decl decls in
  let (events', decls) = List.partition is_event_decl decls in
  let decls = merge_encodings decls in
  let chunks = get_chunks ~previous_chunks:previous_chunks (maps' @ events' @ decls @ impdef_decls) in

  (* Declare operators *)
  let op_ast =
    List.map (Translate_asl.ast_of_declaration ctx) op_decls
    |> concat_ast
  in
  let (checked_op_ast, env) = Type_check.check ctx.tc_env op_ast in
  let ctx = { ctx with tc_env = env } in

  (* Extract constraint assertions from function bodys *)
  let ctx = { ctx with fun_constraints = Translate_asl.get_fun_constraints decls } in

  (* Translate declarations *)
  done_chunks := 0;
  num_chunks := List.length chunks;
  let (checked_ast, ast, ctx) = convert_ast ctx chunks in
  (*let ast = Sail_to_sail.map_ast (update_effects ctx.tc_env) ast in*)

  let chunk_map = List.fold_left (fun m c -> StringMap.add (name_of_chunk c) c m) StringMap.empty chunks in
  let previous_chunks' = StringMap.union (fun _ c1 c2 -> Some (merge_chunks c1 c2)) previous_chunks chunk_map in
  let previous_files' = previous_files @ [ASL_File (filename, decls, append_ast checked_op_ast checked_ast, append_ast op_ast ast)] in
  (ctx, maps @ maps', events @ events', clauses @ clauses', previous_chunks', previous_files')

let process_map_clauses (ctx : Translate_asl.ctx) decls =
  let ast = Translate_asl.ast_of_maps ctx decls in
  report_sail_error ctx decls ast
    (fun _ ->
       let ast = Sail_to_sail.rewrite_make_unique ast in
       let (checked_ast, ast, _env) = iterate_check 0 ctx.tc_env ast in
       ASL_File ("map_clauses.asl", decls, checked_ast, ast))
    (fun _ -> exit 1)

let process_event_clauses (ctx : Translate_asl.ctx) decls =
  let ast = Translate_asl.ast_of_events ctx decls in
  report_sail_error ctx decls ast
    (fun _ ->
       let ast = Sail_to_sail.rewrite_make_unique ast in
       let (checked_ast, ast, _env) = iterate_check 0 ctx.tc_env ast in
       ASL_File ("event_clauses.asl", decls, checked_ast, ast))
    (fun _ -> exit 1)

let process_sail_file ((ctx : Translate_asl.ctx), maps, events, clauses, previous_chunks, previous_files) filename =
  if not !quiet then print_endline ("Reading Sail file " ^ filename);
  let (ast, env, _) =
    try parse_sail_file filename |> Libsail.Frontend.check_ast false ctx.tc_env
    with Reporting.Fatal_error e -> Reporting.print_error e; exit 1
  in
  let previous_files' = previous_files @ [Sail_File (filename, ast)] in
  ({ ctx with tc_env = env }, maps, events, clauses, previous_chunks, previous_files')

let process_file ctx filename =
  if is_asl_filename filename then process_asl_file ctx filename
  else if is_sail_filename filename then process_sail_file ctx filename
  else failwith ("Unrecognised file extension: " ^ filename)

let slice_processed_files fs =
  if !slice_roots = [] then fs else begin
    if not !quiet then print_endline "Slicing specification";
    (* Build dependency graph of full specification *)
    let combined_ast = List.map sail_ast_of_processed_file fs |> List.fold_left append_ast Ast_defs.empty_ast |> Libsail.Scattered.descatter in
    let module NodeSet = Set.Make(Callgraph.Node) in
    let module G = Graph.Make(Callgraph.Node) in
    let g = Callgraph.graph_of_ast combined_ast in
    (* Slice graph *)
    let roots = !slice_roots |> List.map (fun id -> Callgraph.Function (mk_id id)) |> NodeSet.of_list in
    let cuts = !slice_cuts |> List.map (fun id -> Callgraph.Function (mk_id id)) |> NodeSet.of_list in
    let g = G.prune roots cuts g in
    (* Apply pruning to Sail files translated from ASL *)
    let filter_processed_file = function
      | ASL_File (filename, decls, checked_ast, ast) ->
         ASL_File (filename, decls, Callgraph.filter_ast cuts g checked_ast, Callgraph.filter_ast cuts g ast)
      | f -> f
    in
    List.map filter_processed_file fs
  end

let generate_stubs ctx processed_files =
  let stubs =
    if !gen_stubs then begin
      (* Determine declared but not defined functions *)
      if not !quiet then print_endline "Generating stubs for missing functions";
      let decls = List.concat (List.map asl_decls_of_processed_file processed_files) in
      let ast = List.map sail_ast_of_processed_file processed_files |> List.fold_left append_ast Ast_defs.empty_ast |> Libsail.Scattered.descatter in
      let defined_sail_funs = List.map get_fundef_id ast.defs |> List.concat |> IdSet.of_list in
      let is_undefined id =
        let id' = Translate_asl.sail_id_of_ident id in
        not (IdSet.mem id' defined_sail_funs) && IdSet.mem id' (val_spec_ids ast.defs)
      in
      let add_stub stubs = function
        | Decl_FunType (ty, id, args, l) when is_undefined id ->
           ASL_Utils.Bindings.add id (Decl_FunDefn (ty, id, args, [Stmt_FunReturn (Expr_Unknown ty, l)], l)) stubs
        | Decl_ProcType (id, args, l) when is_undefined id ->
           ASL_Utils.Bindings.add id (Decl_ProcDefn (id, args, [Stmt_ProcReturn l], l)) stubs
        | Decl_VarGetterType (ty, id, l) when is_undefined id ->
           ASL_Utils.Bindings.add id (Decl_VarGetterDefn (ty, id, [Stmt_FunReturn (Expr_Unknown ty, l)], l)) stubs
        | Decl_ArrayGetterType (ty, id, args, l) when is_undefined id ->
           ASL_Utils.Bindings.add id (Decl_ArrayGetterDefn (ty, id, args, [Stmt_FunReturn (Expr_Unknown ty, l)], l)) stubs
        | Decl_VarSetterType (id, ty, arg, l) when is_undefined id ->
           ASL_Utils.Bindings.add id (Decl_VarSetterDefn (id, ty, arg, [Stmt_ProcReturn l], l)) stubs
        | Decl_ArraySetterType (id, args, ty, var, l) when is_undefined id ->
           ASL_Utils.Bindings.add id (Decl_ArraySetterDefn (id, args, ty, var, [Stmt_ProcReturn l], l)) stubs
        | _ -> stubs
      in
      let stubs = List.fold_left add_stub ASL_Utils.Bindings.empty decls |> ASL_Utils.Bindings.bindings |> List.map snd in
      let chunks = List.map (fun decl -> Chunk_decls [decl]) stubs in
      let quiet_orig = !quiet in
      quiet := true;
      let (checked_ast, ast, _ctx) = convert_ast ~use_patches:false ctx chunks in
      quiet := quiet_orig;
      [ASL_File ("stubs.asl", stubs, checked_ast, ast)]
    end else []
  in
  processed_files @ stubs

let main () : unit =
  begin
    let input_arg file = input_files := !input_files @ [file] in
    Arg.parse options input_arg "ASL to Sail processor";

    if String.compare !sail_lib_dir "" == 0 then
      sail_lib_dir :=
        let in_ch = Unix.open_process_in "opam var sail:share" in
        let s = input_line in_ch in
        match Unix.close_process_in in_ch with
        | Unix.WEXITED 0 -> s
        | Unix.WEXITED code ->
           failwith ("Failed to find Sail library directory with opam (status " ^ string_of_int code ^ "), maybe use -sail_lib_dir?")
        | Unix.WSIGNALED signal | Unix.WSTOPPED signal ->
           failwith ("Failed to find Sail library directory with opam (" ^ string_of_int signal ^ "), maybe use -sail_lib_dir?")
    else ();

    Reporting.opt_warnings := false;
    Constraint.load_digests ();
    Libsail.Nl_flow.opt_nl_flow := true;
    Type_check.opt_expand_valspec := false; (* Preserve type abbreviations in val-specs for callgraph computation and slicing *)

    (* Set up the context *)
    let ctx = { Translate_asl.empty_ctx with tc_env = Type_check.initial_env } in
    (*Type_check.opt_no_effects := true;*)
    (* Type_check.opt_no_lexp_bounds_check := true; *)
    (* Type_check.opt_new_bitfields := true; *)

    (* Load the Sail prelude for ARM *)
    let ctx = process_sail_file (ctx, [], [], [], StringMap.empty, []) (sail_filename "prelude") in

    (* Load the ASL prelude *)
    let _  = LibASL.LoadASL.read_file "prelude.asl" true false in

    (* Translate files *)
    let (ctx, maps, events, clauses, _, processed_files) = List.fold_left process_file ctx !input_files in
    let processed_files =
      processed_files
      @ [process_map_clauses ctx (maps @ clauses); process_event_clauses ctx (events @ clauses)]
      |> generate_stubs ctx
      |> slice_processed_files
    in
    if not !quiet then print_endline "Writing generated files";
    List.iter write_processed_file processed_files;

    Constraint.save_digests ();
  end

let () =
  if !Sys.interactive then
    ()
  else
    try main () with
    | Type_error (_, err) ->
       prerr_endline "Unhandled type error!";
       prerr_endline (string_of_type_error err |> fst);
       Printexc.print_backtrace stderr;
       exit 1
