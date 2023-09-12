(****************************************************************************)
(*     Sail                                                                 *)
(*                                                                          *)
(*  Sail and the Sail architecture models here, comprising all files and    *)
(*  directories except the ASL-derived Sail code in the aarch64 directory,  *)
(*  are subject to the BSD two-clause licence below.                        *)
(*                                                                          *)
(*  The ASL derived parts of the ARMv8.3 specification in                   *)
(*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               *)
(*                                                                          *)
(*  Copyright (c) 2013-2021                                                 *)
(*    Kathyrn Gray                                                          *)
(*    Shaked Flur                                                           *)
(*    Stephen Kell                                                          *)
(*    Gabriel Kerneis                                                       *)
(*    Robert Norton-Wright                                                  *)
(*    Christopher Pulte                                                     *)
(*    Peter Sewell                                                          *)
(*    Alasdair Armstrong                                                    *)
(*    Brian Campbell                                                        *)
(*    Thomas Bauereiss                                                      *)
(*    Anthony Fox                                                           *)
(*    Jon French                                                            *)
(*    Dominic Mulligan                                                      *)
(*    Stephen Kell                                                          *)
(*    Mark Wassell                                                          *)
(*    Alastair Reid (Arm Ltd)                                               *)
(*                                                                          *)
(*  All rights reserved.                                                    *)
(*                                                                          *)
(*  This work was partially supported by EPSRC grant EP/K008528/1 <a        *)
(*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          *)
(*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   *)
(*  KTF funding, and donations from Arm.  This project has received         *)
(*  funding from the European Research Council (ERC) under the European     *)
(*  Union’s Horizon 2020 research and innovation programme (grant           *)
(*  agreement No 789108, ELVER).                                            *)
(*                                                                          *)
(*  This software was developed by SRI International and the University of  *)
(*  Cambridge Computer Laboratory (Department of Computer Science and       *)
(*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        *)
(*  and FA8750-10-C-0237 ("CTSRD").                                         *)
(*                                                                          *)
(*  Redistribution and use in source and binary forms, with or without      *)
(*  modification, are permitted provided that the following conditions      *)
(*  are met:                                                                *)
(*  1. Redistributions of source code must retain the above copyright       *)
(*     notice, this list of conditions and the following disclaimer.        *)
(*  2. Redistributions in binary form must reproduce the above copyright    *)
(*     notice, this list of conditions and the following disclaimer in      *)
(*     the documentation and/or other materials provided with the           *)
(*     distribution.                                                        *)
(*                                                                          *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''      *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A         *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR     *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,            *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF        *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,      *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF      *)
(*  SUCH DAMAGE.                                                            *)
(****************************************************************************)

open Ast_util
open Ast_defs
open Ast_diff

module StringMap = Map.Make (String)

let opt_ddump_initial_ast = ref false
let opt_ddump_tc_ast = ref false
let opt_reformat : string option ref = ref None

let check_ast (asserts_termination : bool) (env : Type_check.Env.t) (ast : uannot ast) :
    Type_check.tannot ast * Type_check.Env.t * Effects.side_effect_info =
  let ast, env = Type_error.check env ast in
  let ast = Scattered.descatter ast in
  let side_effects = Effects.infer_side_effects asserts_termination ast in
  Effects.check_side_effects side_effects ast;
  let () = if !opt_ddump_tc_ast then Pretty_print_sail.pp_ast stdout (Type_check.strip_ast ast) else () in
  (ast, env, side_effects)

let load_files ?target default_sail_dir options type_envs files =
  let t = Profile.start () in

  let parsed_files = List.map (fun f -> (f, Initial_check.parse_file f)) files in

  let comments = List.map (fun (f, (comments, _)) -> (f, comments)) parsed_files in
  let target_name = Option.map Target.name target in
  let ast =
    Parse_ast.Defs
      (List.map
         (fun (f, (_, file_ast)) -> (f, Preprocess.Defs.preprocess default_sail_dir target_name options file_ast))
         parsed_files
      )
  in
  let ast = Initial_check.process_ast ~generate:true ast in
  let ast = { ast with comments } in

  let () = if !opt_ddump_initial_ast then Pretty_print_sail.pp_ast stdout ast else () in

  begin
    match !opt_reformat with
    | Some dir ->
        Pretty_print_sail.reformat dir ast;
        exit 0
    | None -> ()
  end;

  (* The separate loop measures declarations would be awkward to type check, so
     move them into the definitions beforehand. *)
  let ast = Rewrites.move_loop_measures ast in
  Profile.finish "parsing" t;

  let t = Profile.start () in
  let asserts_termination = Option.fold ~none:false ~some:Target.asserts_termination target in
  let ast, type_envs, side_effects = check_ast asserts_termination type_envs ast in
  Profile.finish "type checking" t;

  (ast, type_envs, side_effects)

let rewrite_ast_initial effect_info env =
  Rewrites.rewrite effect_info env
    [("initial", fun effect_info env ast -> (Rewriter.rewrite_ast ast, effect_info, env))]

let initial_rewrite effect_info type_envs ast =
  let ast, _, _ = rewrite_ast_initial effect_info type_envs ast in
  (* Recheck after descattering so that the internal type environments
     always have complete variant types *)
  Type_error.check Type_check.initial_env (Type_check.strip_ast ast)

let opt_debug_modules = ref true

let module_debug depth msg =
  if !opt_debug_modules then
    prerr_endline (Util.string_of_list "" (fun x -> x) (List.init depth (fun _ -> "| ")) ^ Lazy.force msg)

let mk_mod_id ?loc:(l = Parse_ast.Unknown) ns str = Parse_ast.(Mod_id_aux (Mod_id (ns, str), l))

let string_of_mod_id = Parse_ast.(function Mod_id_aux (Mod_id (namespace, str), _) -> Util.string_of_list "." (fun x -> x) namespace ^ "." ^ str)

let mod_id_loc = Parse_ast.(function Mod_id_aux (_, l) -> l)

module ModId = struct
  open Parse_ast
  type t = mod_id
  let compare mid1 mid2 =
    match (mid1, mid2) with Mod_id_aux (Mod_id (ns1, x), _), Mod_id_aux (Mod_id (ns2, y), _) ->
      Util.lex_ord_list String.compare (x :: ns1) (y :: ns2)
end

module ModIdMap = Map.Make (ModId)
module ModIdSet = Set.Make (ModId)
module ModIdGraph = Graph.Make (ModId)

type mod_inst = { base : Parse_ast.mod_id; args : mod_arg ModIdMap.t }

and mod_arg = MA_parameter of Parse_ast.mod_id | MA_concrete of mod_inst

let mk_mod_inst id = { base = id; args = ModIdMap.empty }

let rec string_of_mod_arg = function
  | MA_parameter id -> string_of_mod_id id
  | MA_concrete inst -> string_of_mod_inst inst

and string_of_mod_args args =
  if ModIdMap.is_empty args then ""
  else
    "("
    ^ Util.string_of_list ", "
        (fun (param, arg) -> string_of_mod_id param ^ " = " ^ string_of_mod_arg arg)
        (ModIdMap.bindings args)
    ^ ")"

and string_of_mod_inst inst = string_of_mod_id inst.base ^ string_of_mod_args inst.args

let rec compare_mod_arg ma1 ma2 =
  match (ma1, ma2) with
  | MA_parameter id1, MA_parameter id2 -> ModId.compare id1 id2
  | MA_concrete inst1, MA_concrete inst2 -> compare_mod_inst inst1 inst2
  | MA_parameter _, _ -> 1
  | _, MA_parameter _ -> -1

and compare_mod_inst inst1 inst2 =
  let lex_ord c1 c2 = if c1 = 0 then c2 else c1 in
  lex_ord (ModId.compare inst1.base inst2.base) (ModIdMap.compare compare_mod_arg inst1.args inst2.args)

module ModArg = struct
  type t = mod_arg
  let compare = compare_mod_arg
end

module ModInst = struct
  type t = mod_inst
  let compare = compare_mod_inst
end

module ModInstMap = Map.Make (ModInst)
module ModInstSet = Set.Make (ModInst)
module ModInstGraph = Graph.Make (ModInst)

let string_of_mod_args args =
  if ModIdMap.is_empty args then ""
  else
    "("
    ^ Util.string_of_list ", "
        (fun (param, arg) -> string_of_mod_id param ^ " = " ^ string_of_mod_arg arg)
        (ModIdMap.bindings args)
    ^ ")"

let string_of_mod_inst inst = string_of_mod_id inst.base ^ string_of_mod_args inst.args

type checked_module = {
  inst : mod_inst;
  file : string;
  defs : Type_check.tannot Ast.def list;
  comments : Lexer.comment list;
  implements : Parse_ast.mod_id option;
  parameters : Parse_ast.parameter list;
  imports : mod_inst list;
}

type interface = {
  inst : mod_inst;
  comments : Lexer.comment list;
  defs : uannot Ast.idef list;
  parameters : Parse_ast.parameter list;
  imports : mod_inst list;
  ctx : Initial_check.ctx;
}

type spec = { mods : checked_module ModInstMap.t; sigs : interface ModInstMap.t }

let empty_spec = { mods = ModInstMap.empty; sigs = ModInstMap.empty }

let interface_defs defs =
  let open Parse_ast in
  List.filter_map (function IDEF_aux (IDEF_def def, def_annot) -> Some (DEF_aux (def, def_annot)) | _ -> None) defs

let interface_graph spec =
  List.fold_left
    (fun g (inst, interface) -> List.fold_left (fun g import -> ModInstGraph.add_edge inst import g) g interface.imports)
    ModInstGraph.empty (ModInstMap.bindings spec.sigs)

let find_source ~suffix ~relative:rel_dir ~sail_dir mod_id =
  let mod_file = string_of_mod_id mod_id ^ suffix in
  let search = [Filename.concat rel_dir mod_file; Filename.concat (Filename.concat sail_dir "lib") mod_file] in
  let rec find_mod = function
    | [] -> None
    | path :: paths -> if Sys.file_exists path then Some path else find_mod paths
  in
  find_mod search

let find_module = find_source ~suffix:".sail"
let find_interface = find_source ~suffix:".saili"

let generate_interface defs =
  let open Ast in
  let rec def_filter def =
    let (DEF_aux (aux, def_annot)) = def in
    let aux_opt =
      match aux with
      | DEF_default ds -> Some (DEF_default ds)
      | DEF_type tdef -> Some (DEF_type tdef)
      | DEF_let lb -> Some (DEF_let lb)
      | DEF_val (VS_aux (VS_val_spec (typschm, id, _), l)) ->
          Some (DEF_val (VS_aux (VS_val_spec (typschm, id, None), l)))
      | DEF_fixity (prec, n, id) -> Some (DEF_fixity (prec, n, id))
      | DEF_overload (id, ids) -> Some (DEF_overload (id, ids))
      | DEF_register (DEC_aux (DEC_reg (typ, id, _), l)) -> Some (DEF_register (DEC_aux (DEC_reg (typ, id, None), l)))
      | DEF_outcome (os, defs) -> Some (DEF_outcome (os, List.filter_map def_filter defs))
      | DEF_instantiation (id, substs) -> Some (DEF_instantiation (id, substs))
      | DEF_pragma (name, arg, l) -> Some (DEF_pragma (name, arg, l))
      | DEF_scattered (SD_aux (sd_aux, sd_l)) -> begin
          match sd_aux with
          | SD_funcl _ | SD_mapcl _ | SD_unioncl _ | SD_enumcl _ -> None
          | SD_function _ | SD_variant _ | SD_mapping _ | SD_enum _ | SD_end _ ->
              Some (DEF_scattered (SD_aux (sd_aux, sd_l)))
        end
      | DEF_fundef _ | DEF_mapdef _ | DEF_internal_mutrec _ | DEF_loop_measures _ | DEF_measure _ | DEF_impl _ -> None
    in
    Option.map (fun aux -> DEF_aux (aux, def_annot)) aux_opt
  in
  List.filter_map
    (fun def ->
      def_filter def
      |> Option.map (fun (DEF_aux (aux, def_annot)) -> Type_check.strip_idef (IDEF_aux (IDEF_def aux, def_annot)))
    )
    defs

let check_interface_unique ~diff def l =
  let open Error_format in
  function
  | [] -> raise (Reporting.err_general l "No matching definition in interface")
  | [(idef, _)] -> begin
      match diff def idef with
      | Ok () -> ()
      | Error (l1, l2) ->
          let msg =
            Seq
              [
                Line "Definitions in module and interface are incompatible. They differ in the following way:";
                Line "";
                Location ("", None, l1, Line "Definition in module");
                Location ("", None, l2, Line "Definition in interface");
              ]
          in
          let buf = Buffer.create 1024 in
          format_message msg { (buffer_formatter buf) with loc_color = Util.cyan };
          raise (Reporting.err_general l (Buffer.contents buf))
    end
  | (_, l1) :: (_, l2) :: _ ->
      let msg =
        Seq
          [
            Line "Duplicate definitions in interface:";
            Line "";
            Location ("", None, l1, Line "First definition is here");
            Location ("", None, l2, Line "Second definition is here");
          ]
      in
      let buf = Buffer.create 1024 in
      format_message msg { (buffer_formatter buf) with loc_color = Util.cyan };
      raise (Reporting.err_general l (Buffer.contents buf))

let rec check_interface defs idefs =
  let open Ast in
  let ( let* ) = Result.bind in
  match defs with
  | DEF_aux (aux, def_annot) :: defs -> begin
      match aux with
      | DEF_register reg ->
          let is_ireg = function
            | IDEF_aux (IDEF_def (DEF_register ireg), def_annot)
              when Id.compare (id_of_dec_spec reg) (id_of_dec_spec ireg) = 0 ->
                Ok (ireg, def_annot.loc)
            | idef -> Error idef
          in
          let diff reg ireg =
            if Option.is_none (register_default ireg) then diff_register (remove_register_default reg) ireg
            else diff_register reg ireg
          in
          let matches, idefs = Util.map_split is_ireg idefs in
          check_interface_unique ~diff reg def_annot.loc matches;
          check_interface defs idefs
      | DEF_type td ->
          let is_td = function
            | IDEF_aux (IDEF_def (DEF_type itd), def_annot) when Id.compare (id_of_type_def td) (id_of_type_def itd) = 0
              ->
                Ok (Ok itd, def_annot.loc)
            | IDEF_aux (IDEF_type (id, typq, kind), def_annot) when Id.compare (id_of_type_def td) id = 0 ->
                Ok (Error (typq, kind), def_annot.loc)
            | idef -> Error idef
          in
          let diff td = function
            | Ok itd -> diff_type_def td itd
            | Error (itypq, ikind) ->
                let typq, kind = typquant_of_type_def td in
                let* () = diff_typquant typq itypq in
                diff_kind kind ikind
          in
          let matches, idefs = Util.map_split is_td idefs in
          check_interface_unique ~diff td def_annot.loc matches;
          check_interface defs idefs
      | DEF_val vs ->
          let is_vs = function
            | IDEF_aux (IDEF_def (DEF_val ivs), def_annot) when Id.compare (id_of_val_spec vs) (id_of_val_spec ivs) = 0
              ->
                Ok (Ok ivs, def_annot.loc)
            | IDEF_aux (IDEF_val id, def_annot) when Id.compare (id_of_val_spec vs) id = 0 ->
                Ok (Error id, def_annot.loc)
            | idef -> Error idef
          in
          let diff vs = function
            | Ok ivs -> diff_val_spec (remove_extern vs) ivs
            | Error id -> diff_id (id_of_val_spec vs) id
          in
          let matches, idefs = Util.map_split is_vs idefs in
          check_interface_unique ~diff vs def_annot.loc matches;
          check_interface defs idefs
      | DEF_let lb ->
          let same_ids ids = IdSet.equal (pat_ids (letbind_pat lb)) ids in
          let is_lb = function
            | IDEF_aux (IDEF_def (DEF_let ilb), def_annot) when same_ids (pat_ids (letbind_pat ilb)) ->
                Ok (Ok ilb, def_annot.loc)
            | IDEF_aux (IDEF_let pat, def_annot) when same_ids (pat_ids pat) -> Ok (Error pat, def_annot.loc)
            | idef -> Error idef
          in
          let diff lb = function Ok ilb -> diff_letbind lb ilb | Error pat -> diff_pat (letbind_pat lb) pat in
          let matches, idefs = Util.map_split is_lb idefs in
          check_interface_unique ~diff lb def_annot.loc matches;
          check_interface defs idefs
      | DEF_pragma _ | DEF_fundef _ | DEF_mapdef _ | DEF_internal_mutrec _ | DEF_loop_measures _ | DEF_measure _
      | DEF_impl _ ->
          check_interface defs idefs
    end
  | [] -> ()

let rec resolve_parameters ?(depth = 0) ?target ~relative ~sail_dir ~options params inst spec =
  module_debug depth (lazy (Util.("Resolve parameters " |> cyan |> clear) ^ string_of_mod_inst inst));
  let open Parse_ast in
  let old_args = ref inst.args in
  let interfaces, new_args, spec =
    List.fold_left
      (fun (interfaces, args, spec) (Parameter_aux (Parameter (name, sig_id), l)) ->
        match ModIdMap.find_opt name !old_args with
        | Some (MA_parameter sig_id' as arg) ->
            if ModId.compare sig_id sig_id' = 0 then (
              old_args := ModIdMap.remove name !old_args;
              let interface, spec =
                load_interface ~depth:(depth + 1) ?target ~relative ~sail_dir ~options (mk_mod_inst sig_id) spec
              in
              (interface :: interfaces, ModIdMap.add name arg args, spec)
            )
            else raise (Reporting.err_general l "Invalid module parameter")
        | Some (MA_concrete inst as arg) ->
            old_args := ModIdMap.remove name !old_args;
            let interface, spec = load_interface ~depth:(depth + 1) ?target ~relative ~sail_dir ~options inst spec in
            (interface :: interfaces, ModIdMap.add name arg args, spec)
        | None ->
            let interface, spec =
              load_interface ~depth:(depth + 1) ?target ~relative ~sail_dir ~options (mk_mod_inst sig_id) spec
            in
            begin
              match interface.parameters with
              | Parameter_aux (_, s_l) :: _ ->
                  raise
                    (Reporting.err_general
                       (Hint ("Forbidden parameter is here", s_l, mod_id_loc sig_id))
                       "parameter type may not itself contain any parameters"
                    )
              | [] -> ()
            end;
            module_debug depth
              ( lazy
                ("Adding parameter " ^ string_of_mod_id name ^ " = " ^ string_of_mod_id sig_id ^ " to instantiation")
                );
            (interface :: interfaces, ModIdMap.add name (MA_parameter sig_id) args, spec)
      )
      ([], ModIdMap.empty, spec) params
  in
  (interfaces, { inst with args = new_args }, spec)

and resolve_imports ?(depth = 0) ?target ~relative ~sail_dir ~options parent_inst imports spec =
  module_debug depth (lazy (Util.("Resolve imports " |> cyan |> clear) ^ string_of_mod_inst parent_inst));
  let open Parse_ast in
  let interfaces, spec =
    List.fold_left
      (fun (interfaces, spec) (Import_aux (Import mexp, l)) ->
        let child_inst =
          match mexp with
          | ME_aux (ME_app (mod_id, args), _) ->
              module_debug (depth + 1) (lazy Util.("Resolving import " ^ string_of_mod_id mod_id));
              List.fold_left
                (fun child_inst (id, arg) ->
                  match arg with
                  | ME_aux (ME_id arg, _) -> begin
                      match ModIdMap.find_opt arg parent_inst.args with
                      | Some arg ->
                          module_debug (depth + 1) (lazy (string_of_mod_id id ^ " -> " ^ string_of_mod_arg arg));
                          { child_inst with args = ModIdMap.add id arg child_inst.args }
                      | None -> child_inst
                    end
                  | _ -> child_inst
                )
                { base = mod_id; args = ModIdMap.empty }
                args
          | ME_aux (ME_id mod_id, _) -> { base = mod_id; args = ModIdMap.empty }
        in
        module_debug (depth + 1) (lazy Util.(string_of_mod_inst child_inst |> red |> clear));
        let interface, spec = load_interface ~depth:(depth + 1) ?target ~relative ~sail_dir ~options child_inst spec in
        (interface :: interfaces, spec)
      )
      ([], spec) imports
  in
  (List.rev interfaces, spec)

and load_interface ?(depth = 0) ?target ~relative ~sail_dir ~options inst spec =
  module_debug depth (lazy ("Load interface " ^ string_of_mod_inst inst));
  match ModInstMap.find_opt inst spec.sigs with
  | Some interface -> (interface, spec)
  | None -> begin
      match find_interface ~relative ~sail_dir inst.base with
      | Some file -> load_interface_from_file ~depth:(depth + 1) ?target ~sail_dir ~options inst file spec
      | None -> begin
          match find_module ~relative ~sail_dir inst.base with
          | Some file ->
              let interface, _, spec =
                load_module_from_file ~depth:(depth + 1) ?target ~sail_dir ~options inst file spec
              in
              (interface, spec)
          | None ->
              raise
                (Reporting.err_general (mod_id_loc inst.base)
                   ("Failed to find interface or module " ^ string_of_mod_id inst.base)
                )
        end
    end

and load_interface_from_file ?(depth = 0) ?target ~sail_dir ~options inst file spec =
  module_debug depth
    (lazy (Util.("Load interface " |> yellow |> clear) ^ string_of_mod_inst inst ^ " from file " ^ file));
  let comments, parsed_file = Initial_check.parse_interface_file file in
  let target_name = Option.map Target.name target in
  let rel_dir = Filename.dirname file in

  let preprocessed_file = Preprocess.Interface_defs.preprocess sail_dir target_name options parsed_file in

  let parameters = Initial_check.get_parameters (interface_defs parsed_file) in
  let parameter_interfaces, inst, spec =
    resolve_parameters ~depth ?target ~relative:rel_dir ~sail_dir ~options parameters inst spec
  in

  let imports = Initial_check.get_imports (interface_defs preprocessed_file) in
  let interfaces, spec = resolve_imports ~depth ?target ~relative:rel_dir ~sail_dir ~options inst imports spec in
  let imports = List.map (fun s -> s.inst) (parameter_interfaces @ interfaces) in

  let ctx =
    Initial_check.(List.fold_left (fun ctx s -> merge_ctx (mod_id_loc s.inst.base) ctx s.ctx) root_ctx interfaces)
  in

  let defs, ctx = Initial_check.to_idefs ctx parsed_file in

  let interface = { inst; defs; comments; parameters; imports; ctx } in
  (interface, { spec with sigs = ModInstMap.add inst interface spec.sigs })

and load_module_from_file ?(depth = 0) ?target ~sail_dir ~options inst file spec =
  module_debug depth (lazy (Util.("Load module " |> yellow |> clear) ^ string_of_mod_inst inst ^ " from file " ^ file));
  let comments, parsed_file = Initial_check.parse_file file in
  let target_name = Option.map Target.name target in
  let rel_dir = Filename.dirname file in

  let preprocessed_file = Preprocess.Defs.preprocess sail_dir target_name options parsed_file in

  let parameters = Initial_check.get_parameters preprocessed_file in
  let parameter_interfaces, inst, spec =
    resolve_parameters ~depth ?target ~relative:rel_dir ~sail_dir ~options parameters inst spec
  in

  let implements = Initial_check.get_implements preprocessed_file in
  let imports = Initial_check.get_imports preprocessed_file in
  let interfaces, spec = resolve_imports ~depth ?target ~relative:rel_dir ~sail_dir ~options inst imports spec in
  let imports = List.map (fun s -> s.inst) (parameter_interfaces @ interfaces) in
  let ctx =
    Initial_check.(List.fold_left (fun ctx s -> merge_ctx (mod_id_loc s.inst.base) ctx s.ctx) root_ctx interfaces)
  in

  let defs, ctx = Initial_check.to_defs ctx preprocessed_file in

  let ig = interface_graph spec in
  let ig = List.fold_left (fun ig import -> ModInstGraph.add_edge inst import ig) ig imports in
  let transitive_imports : mod_inst list =
    try ModInstGraph.topsort (ModInstGraph.prune (ModInstSet.singleton inst) ModInstSet.empty ig)
    with ModInstGraph.Not_a_DAG _ -> raise (Reporting.err_general (mod_id_loc inst.base) "Cyclic modules found")
  in
  let transitive_imports = match transitive_imports with _ :: tis -> List.rev tis | [] -> [] in

  module_debug depth
    (lazy ("Creating typing environment for: " ^ Util.string_of_list ", " string_of_mod_inst transitive_imports));
  let env =
    List.fold_left
      (fun env ti ->
        let interface = ModInstMap.find ti spec.sigs in
        Type_error.check_interface env interface.defs
      )
      Type_check.initial_env transitive_imports
  in

  let defs, _ = Type_error.check_defs env defs in
  let md = { inst; file; defs; comments; implements; parameters; imports } in

  match implements with
  | Some interface ->
      let interface, spec =
        load_interface ~depth:(depth + 1) ?target ~relative:rel_dir ~sail_dir ~options (mk_mod_inst interface) spec
      in
      check_interface defs interface.defs;

      (interface, md, { spec with mods = ModInstMap.add inst md spec.mods })
  | None ->
      let sig_defs = generate_interface defs in

      module_debug depth (lazy (Util.("Loaded " |> green |> clear) ^ file ^ " as " ^ string_of_mod_inst inst));

      let interface = { inst; defs = sig_defs; comments = []; parameters; imports; ctx } in

      (interface, md, { sigs = ModInstMap.add inst interface spec.sigs; mods = ModInstMap.add inst md spec.mods })
