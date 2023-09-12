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

open Parse_ast

(* Simple preprocessor features for conditional file loading *)
module StringSet = Set.Make (String)

let default_symbols =
  List.fold_left
    (fun set str -> StringSet.add str set)
    StringSet.empty
    ["FEATURE_IMPLICITS"; "FEATURE_CONSTANT_TYPES"; "FEATURE_BITVECTOR_TYPE"; "FEATURE_UNION_BARRIER"]

let symbols = ref default_symbols

let have_symbol symbol = StringSet.mem symbol !symbols

let clear_symbols () = symbols := default_symbols

let add_symbol str = symbols := StringSet.add str !symbols

let () =
  let open Interactive in
  ArgString ("symbol", fun symbol -> ActionUnit (fun _ -> add_symbol symbol))
  |> register_command ~name:"define_symbol" ~help:"Define preprocessor symbol";

  ArgString ("symbol", fun symbol -> ActionUnit (fun _ -> symbols := StringSet.remove symbol !symbols))
  |> register_command ~name:"undef_symbol" ~help:"Undefine preprocessor symbol";

  ActionUnit (fun _ -> List.iter print_endline (StringSet.elements !symbols))
  |> register_command ~name:"symbols" ~help:"Print defined preprocessor symbols"

(* We want to provide warnings for e.g. a mispelled pragma rather than
   just silently ignoring them, so we have a list here of all
   recognised pragmas. *)
let all_pragmas =
  List.fold_left
    (fun set str -> StringSet.add str set)
    StringSet.empty
    [
      "define";
      "anchor";
      "span";
      "include";
      "ifdef";
      "ifndef";
      "iftarget";
      "else";
      "endif";
      "option";
      "optimize";
      "latex";
      "property";
      "counterexample";
      "suppress_warnings";
      "include_start";
      "include_end";
      "sail_internal";
      "target_set";
      "non_exec";
      "vector_order";
    ]

let to_order_pragma l = function
  | Parse_ast.ATyp_inc -> Some ("vector_order", "inc", l)
  | Parse_ast.ATyp_dec -> Some ("vector_order", "dec", l)
  | _ -> None

module type PRAGMA = sig
  type def

  val destruct_pragma : def -> (string * string * Parse_ast.l) option

  val mk_pragma : string -> string -> Parse_ast.l -> def

  val recur : (def list -> def list) -> def -> def

  val parse_file : ?loc:Parse_ast.l -> string -> Lexer.comment list * def list
end

module Def_pragma = struct
  type def = Parse_ast.def

  let destruct_pragma = function
    | DEF_aux (DEF_default (DT_aux (DT_order (_, ATyp_aux (atyp, _)), _)), l) -> to_order_pragma l atyp
    | DEF_aux (DEF_pragma (name, arg), l) -> Some (name, arg, l)
    | def -> None

  let mk_pragma name arg l = DEF_aux (DEF_pragma (name, arg), l)

  let recur f = function
    | DEF_aux (DEF_outcome (outcome_spec, inner_defs), l) -> DEF_aux (DEF_outcome (outcome_spec, f inner_defs), l)
    | def -> def

  let parse_file = Initial_check.parse_file
end

module Interface_def_pragma = struct
  type def = Parse_ast.idef

  let destruct_pragma = function
    | IDEF_aux (IDEF_def (DEF_default (DT_aux (DT_order (_, ATyp_aux (atyp, _)), _))), l) -> to_order_pragma l atyp
    | IDEF_aux (IDEF_def (DEF_pragma (name, arg)), l) -> Some (name, arg, l)
    | def -> None

  let mk_pragma name arg l = IDEF_aux (IDEF_def (DEF_pragma (name, arg)), l)

  let recur _ def = def

  let parse_file = Initial_check.parse_interface_file
end

module type S = sig
  type def

  val preprocess : string -> string option -> (Arg.key * Arg.spec * Arg.doc) list -> def list -> def list
end

module Make (P : PRAGMA) : S with type def = P.def = struct
  type def = P.def

  let wrap_include l file = function
    | [] -> []
    | defs -> [P.mk_pragma "include_start" file l] @ defs @ [P.mk_pragma "include_end" file l]

  let cond_pragma l defs =
    let depth = ref 0 in
    let in_then = ref true in
    let then_defs = ref [] in
    let else_defs = ref [] in

    let push_def def = if !in_then then then_defs := def :: !then_defs else else_defs := def :: !else_defs in

    let rec scan = function
      | def :: defs -> begin
          match P.destruct_pragma def with
          | Some ("endif", _, _) when !depth = 0 -> (List.rev !then_defs, List.rev !else_defs, defs)
          | Some ("else", _, _) when !depth = 0 ->
              in_then := false;
              scan defs
          | Some (p, _, _) when p = "ifdef" || p = "ifndef" || p = "iftarget" ->
              incr depth;
              push_def def;
              scan defs
          | Some ("endif", _, _) ->
              decr depth;
              push_def def;
              scan defs
          | _ ->
              push_def def;
              scan defs
        end
      | [] -> raise (Reporting.err_general l "$ifdef, $ifndef, or $iftarget never ended by $endif")
    in
    scan defs

  let preprocess dir target opts =
    let rec aux acc = function
      | [] -> List.rev acc
      | def :: defs -> (
          match P.destruct_pragma def with
          | Some ("define", symbol, _) ->
              symbols := StringSet.add symbol !symbols;
              aux acc defs
          | Some ("option", command, l) ->
              begin
                let first_line err_msg =
                  match String.split_on_char '\n' err_msg with line :: _ -> "\n" ^ line | [] -> ("" [@coverage off])
                  (* Don't expect this should ever happen, but we are fine if it does *)
                in
                try
                  let args = Str.split (Str.regexp " +") command in
                  let file_arg file =
                    raise
                      (Reporting.err_general l
                         ("Anonymous argument '" ^ file ^ "' cannot be passed via $option directive")
                      )
                  in
                  Arg.parse_argv ~current:(ref 0) (Array.of_list ("sail" :: args)) opts file_arg ""
                with
                | Arg.Help msg -> raise (Reporting.err_general l "-help flag passed to $option directive")
                | Arg.Bad msg ->
                    raise (Reporting.err_general l ("Invalid flag passed to $option directive" ^ first_line msg))
              end;
              aux (def :: acc) defs
          | Some ("ifndef", symbol, l) ->
              let then_defs, else_defs, defs = cond_pragma l defs in
              if not (StringSet.mem symbol !symbols) then aux acc (then_defs @ defs) else aux acc (else_defs @ defs)
          | Some ("ifdef", symbol, l) ->
              let then_defs, else_defs, defs = cond_pragma l defs in
              if StringSet.mem symbol !symbols then aux acc (then_defs @ defs) else aux acc (else_defs @ defs)
          | Some ("iftarget", t, l) ->
              let then_defs, else_defs, defs = cond_pragma l defs in
              begin
                match target with Some t' when t = t' -> aux acc (then_defs @ defs) | _ -> aux acc (else_defs @ defs)
              end
          | Some ("include", file, l) ->
              let len = String.length file in
              if len = 0 then (
                Reporting.warn "" l "Skipping bad $include. No file argument.";
                aux acc defs
              )
              else if file.[0] = '"' && file.[len - 1] = '"' then (
                let relative =
                  match l with
                  | Parse_ast.Range (pos, _) -> Filename.dirname Lexing.(pos.pos_fname)
                  | _ -> failwith "Couldn't figure out relative path for $include. This really shouldn't ever happen."
                in
                let file = String.sub file 1 (len - 2) in
                let include_file = Filename.concat relative file in
                let include_defs = P.parse_file ~loc:l (Filename.concat relative file) |> snd |> aux [] in
                aux (List.rev (wrap_include l include_file include_defs) @ acc) defs
              )
              else if file.[0] = '<' && file.[len - 1] = '>' then (
                let file = String.sub file 1 (len - 2) in
                let sail_dir = Reporting.get_sail_dir dir in
                let file = Filename.concat sail_dir ("lib/" ^ file) in
                let include_defs = P.parse_file ~loc:l file |> snd |> aux [] in
                aux (List.rev (wrap_include l file include_defs) @ acc) defs
              )
              else (
                let help = "Make sure the filename is surrounded by quotes or angle brackets" in
                Reporting.warn "" l ("Skipping bad $include " ^ file ^ ". " ^ help);
                aux acc defs
              )
          | Some ("suppress_warnings", _, l) ->
              begin
                match Reporting.simp_loc l with
                | None -> () (* This shouldn't happen, but if it does just continue *)
                | Some (p, _) -> Reporting.suppress_warnings_for_file p.pos_fname
              end;
              aux acc defs
          (* Filter file_start and file_end out of the AST so when we
             round-trip files through the compiler we don't end up with
             incorrect start/end annotations *)
          | Some ("file_start", _, _) | Some ("file_end", _, _) -> aux acc defs
          | Some ("vector_order", "inc", _) ->
              symbols := StringSet.add "_DEFAULT_INC" !symbols;
              aux (def :: acc) defs
          | Some ("vector_order", "dec", _) ->
              symbols := StringSet.add "_DEFAULT_DEC" !symbols;
              aux (def :: acc) defs
          | Some (p, _, l) ->
              if not (StringSet.mem p all_pragmas) then Reporting.warn "" l ("Unrecognised directive: " ^ p);
              aux (def :: acc) defs
          | None ->
              let def = P.recur (aux []) def in
              aux (def :: acc) defs
        )
    in
    aux []
end

module Defs = Make (Def_pragma)
module Interface_defs = Make (Interface_def_pragma)
