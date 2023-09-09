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
(*  Copyright (c) 2013-2023                                                 *)
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

module Big_int = Nat_big_num

open Ast
open Ast_util

let ( let* ) = Result.bind

let rec diff_list length_err f xs ys =
  match (xs, ys) with
  | [], [] -> Ok ()
  | _, [] -> Error length_err
  | [], _ -> Error length_err
  | x :: xs, y :: ys ->
      let* () = f x y in
      diff_list length_err f xs ys

let diff_option mismatch_err f x y =
  match (x, y) with
  | None, None -> Ok ()
  | Some _, None -> Error mismatch_err
  | None, Some _ -> Error mismatch_err
  | Some x, Some y -> f x y

let diff_kid v1 v2 = if Kid.compare v1 v2 = 0 then Ok () else Error (kid_loc v1, kid_loc v2)

let diff_kind (K_aux (k1, l1)) (K_aux (k2, l2)) = if k1 = k2 then Ok () else Error (l1, l2)

let diff_id id1 id2 = if Id.compare id1 id2 = 0 then Ok () else Error (id_loc id1, id_loc id2)

(* Treat 0x0000_0000 and 0x00000000 the same *)
let equal_bv_lit str1 str2 = List.equal String.equal (String.split_on_char '_' str1) (String.split_on_char '_' str2)

(* In the following functions we avoid writing full wildcard patterns
   like `_, _` as we want to ensure we get warnings when new
   constructors are added to the AST. *)

let diff_lit (L_aux (lit1, l1)) (L_aux (lit2, l2)) =
  match (lit1, lit2) with
  | L_unit, L_unit -> Ok ()
  | L_zero, L_zero -> Ok ()
  | L_one, L_one -> Ok ()
  | L_true, L_true -> Ok ()
  | L_false, L_false -> Ok ()
  | L_num n1, L_num n2 -> if Big_int.equal n1 n2 then Ok () else Error (l1, l2)
  | L_hex str1, L_hex str2 -> if equal_bv_lit str1 str2 then Ok () else Error (l1, l2)
  | L_bin str1, L_bin str2 -> if equal_bv_lit str1 str2 then Ok () else Error (l1, l2)
  | L_string str1, L_string str2 -> if String.equal str1 str2 then Ok () else Error (l1, l2)
  | L_undef, L_undef -> Ok ()
  | L_real str1, L_real str2 -> if String.equal str1 str2 then Ok () else Error (l1, l2)
  | (L_unit | L_zero | L_one | L_true | L_false | L_num _ | L_hex _ | L_bin _ | L_string _ | L_undef | L_real _), _ ->
      Error (l1, l2)

let diff_kinded_id (KOpt_aux (KOpt_kind (k1, v1), l1)) (KOpt_aux (KOpt_kind (k2, v2), l2)) =
  let* () = diff_kid v1 v2 in
  diff_kind k1 k2

let rec diff_nexp (Nexp_aux (n1, l1)) (Nexp_aux (n2, l2)) =
  match (n1, n2) with
  | Nexp_id id1, Nexp_id id2 -> diff_id id1 id2
  | Nexp_var v1, Nexp_var v2 -> diff_kid v1 v2
  | Nexp_constant n1, Nexp_constant n2 -> if Big_int.equal n1 n2 then Ok () else Error (l1, l2)
  | Nexp_app (f1, nexps1), Nexp_app (f2, nexps2) ->
      let* () = diff_id f1 f2 in
      diff_list (l1, l2) diff_nexp nexps1 nexps2
  | Nexp_times (lhs1, rhs1), Nexp_times (lhs2, rhs2) ->
      let* () = diff_nexp lhs1 lhs2 in
      diff_nexp rhs1 rhs2
  | Nexp_sum (lhs1, rhs1), Nexp_sum (lhs2, rhs2) ->
      let* () = diff_nexp lhs1 lhs2 in
      diff_nexp rhs1 rhs2
  | Nexp_minus (lhs1, rhs1), Nexp_minus (lhs2, rhs2) ->
      let* () = diff_nexp lhs1 lhs2 in
      diff_nexp rhs1 rhs2
  | Nexp_exp n1, Nexp_exp n2 -> diff_nexp n1 n2
  | Nexp_neg n1, Nexp_neg n2 -> diff_nexp n1 n2
  | ( ( Nexp_id _ | Nexp_var _ | Nexp_constant _ | Nexp_app _ | Nexp_times _ | Nexp_sum _ | Nexp_minus _ | Nexp_exp _
      | Nexp_neg _ ),
      _ ) ->
      Error (l1, l2)

let rec diff_constraint (NC_aux (nc1, l1)) (NC_aux (nc2, l2)) =
  match (nc1, nc2) with
  | NC_equal (lhs1, rhs1), NC_equal (lhs2, rhs2) ->
      let* () = diff_nexp lhs1 lhs2 in
      diff_nexp rhs1 rhs2
  | NC_bounded_ge (lhs1, rhs1), NC_bounded_ge (lhs2, rhs2) ->
      let* () = diff_nexp lhs1 lhs2 in
      diff_nexp rhs1 rhs2
  | NC_bounded_gt (lhs1, rhs1), NC_bounded_gt (lhs2, rhs2) ->
      let* () = diff_nexp lhs1 lhs2 in
      diff_nexp rhs1 rhs2
  | NC_bounded_le (lhs1, rhs1), NC_bounded_le (lhs2, rhs2) ->
      let* () = diff_nexp lhs1 lhs2 in
      diff_nexp rhs1 rhs2
  | NC_bounded_lt (lhs1, rhs1), NC_bounded_lt (lhs2, rhs2) ->
      let* () = diff_nexp lhs1 lhs2 in
      diff_nexp rhs1 rhs2
  | NC_not_equal (lhs1, rhs1), NC_not_equal (lhs2, rhs2) ->
      let* () = diff_nexp lhs1 lhs2 in
      diff_nexp rhs1 rhs2
  | NC_set (v1, nums1), NC_set (v2, nums2) ->
      let* () = diff_kid v1 v2 in
      if List.equal Big_int.equal nums1 nums2 then Ok () else Error (l1, l2)
  | NC_or (lhs1, rhs1), NC_or (lhs2, rhs2) ->
      let* () = diff_constraint lhs1 lhs2 in
      diff_constraint rhs1 rhs2
  | NC_and (lhs1, rhs1), NC_and (lhs2, rhs2) ->
      let* () = diff_constraint lhs1 lhs2 in
      diff_constraint rhs1 rhs2
  | NC_app (f1, args1), NC_app (f2, args2) ->
      let* () = diff_id f1 f2 in
      diff_list (l1, l2) diff_typ_arg args1 args2
  | NC_var v1, NC_var v2 -> diff_kid v1 v2
  | NC_true, NC_true -> Ok ()
  | NC_false, NC_false -> Ok ()
  | ( ( NC_equal _ | NC_bounded_ge _ | NC_bounded_gt _ | NC_bounded_le _ | NC_bounded_lt _ | NC_not_equal _ | NC_set _
      | NC_or _ | NC_and _ | NC_app _ | NC_var _ | NC_true | NC_false ),
      _ ) ->
      Error (l1, l2)

and diff_typ_arg (A_aux (a1, l1)) (A_aux (a2, l2)) =
  match (a1, a2) with
  | A_nexp n1, A_nexp n2 -> diff_nexp n1 n2
  | A_typ typ1, A_typ typ2 -> diff_typ typ1 typ2
  | A_bool nc1, A_bool nc2 -> diff_constraint nc1 nc2
  | (A_nexp _ | A_typ _ | A_bool _), _ -> Error (l1, l2)

and diff_typ (Typ_aux (typ1, l1)) (Typ_aux (typ2, l2)) =
  match (typ1, typ2) with
  | Typ_internal_unknown, Typ_internal_unknown -> Ok ()
  | Typ_id id1, Typ_id id2 -> diff_id id1 id2
  | Typ_var v1, Typ_var v2 -> diff_kid v1 v2
  | Typ_fn (typs1, ret_typ1), Typ_fn (typs2, ret_typ2) ->
      let* () = diff_list (l1, l2) diff_typ typs1 typs2 in
      diff_typ ret_typ1 ret_typ2
  | Typ_bidir (lhs1, rhs1), Typ_bidir (lhs2, rhs2) ->
      let* () = diff_typ lhs1 lhs2 in
      diff_typ rhs1 rhs2
  | Typ_tuple typs1, Typ_tuple typs2 -> diff_list (l1, l2) diff_typ typs1 typs2
  | Typ_app (f1, args1), Typ_app (f2, args2) ->
      let* () = diff_id f1 f2 in
      diff_list (l1, l2) diff_typ_arg args1 args2
  | Typ_exist (vs1, nc1, typ1), Typ_exist (vs2, nc2, typ2) ->
      let* () = diff_list (l1, l2) diff_kinded_id vs1 vs2 in
      let* () = diff_constraint nc1 nc2 in
      diff_typ typ1 typ2
  | (Typ_internal_unknown | Typ_id _ | Typ_var _ | Typ_fn _ | Typ_bidir _ | Typ_tuple _ | Typ_app _ | Typ_exist _), _ ->
      Error (l1, l2)

let diff_quant_item (QI_aux (qi1, l1)) (QI_aux (qi2, l2)) =
  match (qi1, qi2) with
  | QI_id kopt1, QI_id kopt2 -> diff_kinded_id kopt1 kopt2
  | QI_constraint nc1, QI_constraint nc2 -> diff_constraint nc1 nc2
  | (QI_id _ | QI_constraint _), _ -> Error (l1, l2)

let diff_typquant (TypQ_aux (typq1, l1)) (TypQ_aux (typq2, l2)) =
  match (typq1, typq2) with
  | (TypQ_tq [] | TypQ_no_forall), (TypQ_tq [] | TypQ_no_forall) -> Ok ()
  | TypQ_tq qis1, TypQ_tq qis2 -> diff_list (l1, l2) diff_quant_item qis1 qis2
  | (TypQ_no_forall | TypQ_tq _), _ -> Error (l1, l2)

let diff_typschm (TypSchm_aux (TypSchm_ts (typq1, typ1), _)) (TypSchm_aux (TypSchm_ts (typq2, typ2), _)) =
  let* () = diff_typquant typq1 typq2 in
  diff_typ typ1 typ2

let diff_tannot_opt (Typ_annot_opt_aux (t1, l1)) (Typ_annot_opt_aux (t2, l2)) =
  match (t1, t2) with
  | Typ_annot_opt_none, Typ_annot_opt_none -> Ok ()
  | Typ_annot_opt_some (typq1, typ1), Typ_annot_opt_some (typq2, typ2) ->
      let* () = diff_typquant typq1 typq2 in
      diff_typ typ1 typ2
  | (Typ_annot_opt_none | Typ_annot_opt_some _), _ -> Error (l1, l2)

let diff_type_union (Tu_aux (Tu_ty_id (typ1, id1), _)) (Tu_aux (Tu_ty_id (typ2, id2), _)) =
  let* () = diff_id id1 id2 in
  diff_typ typ1 typ2

let rec diff_index_range (BF_aux (ir1, l1)) (BF_aux (ir2, l2)) =
  match (ir1, ir2) with
  | BF_single n1, BF_single n2 -> diff_nexp n1 n2
  | BF_range (n1, m1), BF_range (n2, m2) ->
      let* () = diff_nexp n1 n2 in
      diff_nexp m1 m2
  | BF_concat (lhs1, rhs1), BF_concat (lhs2, rhs2) ->
      let* () = diff_index_range lhs1 lhs2 in
      diff_index_range rhs1 rhs2
  | (BF_single _ | BF_range _ | BF_concat _), _ -> Error (l1, l2)

let diff_type_def (TD_aux (td1, (l1, _))) (TD_aux (td2, (l2, _))) =
  match (td1, td2) with
  | TD_abbrev (id1, typq1, arg1), TD_abbrev (id2, typq2, arg2) ->
      let* () = diff_id id1 id2 in
      let* () = diff_typquant typq1 typq2 in
      diff_typ_arg arg1 arg2
  | TD_record (id1, typq1, fields1, _), TD_record (id2, typq2, fields2, _) ->
      let* () = diff_id id1 id2 in
      let* () = diff_typquant typq1 typq2 in
      diff_list (l1, l2)
        (fun (typ1, id1) (typ2, id2) ->
          let* () = diff_id id1 id2 in
          diff_typ typ1 typ2
        )
        fields1 fields2
  | TD_variant (id1, typq1, tus1, _), TD_variant (id2, typq2, tus2, _) ->
      let* () = diff_id id1 id2 in
      let* () = diff_typquant typq1 typq2 in
      diff_list (l1, l2) diff_type_union tus1 tus2
  | TD_enum (id1, ids1, _), TD_enum (id2, ids2, _) ->
      let* () = diff_id id1 id2 in
      diff_list (l1, l2) diff_id ids1 ids2
  | TD_bitfield (id1, typ1, irs1), TD_bitfield (id2, typ2, irs2) ->
      let* () = diff_id id1 id2 in
      let* () = diff_typ typ1 typ2 in
      diff_list (l1, l2)
        (fun (id1, ir1) (id2, ir2) ->
          let* () = diff_id id1 id2 in
          diff_index_range ir1 ir2
        )
        irs1 irs2
  | (TD_abbrev _ | TD_record _ | TD_variant _ | TD_enum _ | TD_bitfield _), _ -> Error (l1, l2)

let rec diff_typ_pat (TP_aux (tp1, l1)) (TP_aux (tp2, l2)) =
  match (tp1, tp2) with
  | TP_wild, TP_wild -> Ok ()
  | TP_var v1, TP_var v2 -> diff_kid v1 v2
  | TP_app (f1, tps1), TP_app (f2, tps2) ->
      let* () = diff_id f1 f2 in
      diff_list (l1, l2) diff_typ_pat tps1 tps2
  | (TP_wild | TP_var _ | TP_app _), _ -> Error (l1, l2)

let rec diff_pat (P_aux (pat1, (l1, _))) (P_aux (pat2, (l2, _))) =
  match (pat1, pat2) with
  | P_lit lit1, P_lit lit2 -> diff_lit lit1 lit2
  | P_wild, P_wild -> Ok ()
  | P_or (lhs1, rhs1), P_or (lhs2, rhs2) ->
      let* () = diff_pat lhs1 lhs2 in
      diff_pat rhs1 rhs2
  | P_not pat1, P_not pat2 -> diff_pat pat1 pat2
  | P_as (pat1, id1), P_as (pat2, id2) ->
      let* () = diff_id id1 id2 in
      diff_pat pat1 pat2
  | P_typ (typ1, pat1), P_typ (typ2, pat2) ->
      let* () = diff_pat pat1 pat2 in
      diff_typ typ1 typ2
  | P_id id1, P_id id2 -> diff_id id1 id2
  | P_var (pat1, tp1), P_var (pat2, tp2) ->
      let* () = diff_pat pat1 pat2 in
      diff_typ_pat tp1 tp2
  | P_app (f1, pats1), P_app (f2, pats2) ->
      let* () = diff_id f1 f2 in
      diff_list (l1, l2) diff_pat pats1 pats2
  | P_vector pats1, P_vector pats2 -> diff_list (l1, l2) diff_pat pats1 pats2
  | P_vector_concat pats1, P_vector_concat pats2 -> diff_list (l1, l2) diff_pat pats1 pats2
  | P_vector_subrange (id1, n1, m1), P_vector_subrange (id2, n2, m2) ->
      let* () = diff_id id1 id2 in
      if Big_int.equal n1 n2 && Big_int.equal m1 m2 then Ok () else Error (l1, l2)
  | P_tuple pats1, P_tuple pats2 -> diff_list (l1, l2) diff_pat pats1 pats2
  | P_list pats1, P_list pats2 -> diff_list (l1, l2) diff_pat pats1 pats2
  | P_cons (hd_pat1, tl_pat1), P_cons (hd_pat2, tl_pat2) ->
      let* () = diff_pat hd_pat1 hd_pat2 in
      diff_pat tl_pat1 tl_pat2
  | P_string_append pats1, P_string_append pats2 -> diff_list (l1, l2) diff_pat pats1 pats2
  | P_struct (fields1, wild1), P_struct (fields2, wild2) ->
      let* () =
        match (wild1, wild2) with
        | FP_wild _, FP_wild _ -> Ok ()
        | FP_no_wild, FP_no_wild -> Ok ()
        | (FP_wild _ | FP_no_wild), _ -> Error (l1, l2)
      in
      diff_list (l1, l2)
        (fun (id1, pat1) (id2, pat2) ->
          let* () = diff_id id1 id2 in
          diff_pat pat1 pat2
        )
        fields1 fields2
  | ( ( P_lit _ | P_wild | P_or _ | P_not _ | P_as _ | P_typ _ | P_id _ | P_var _ | P_app _ | P_vector _
      | P_vector_concat _ | P_vector_subrange _ | P_tuple _ | P_list _ | P_cons _ | P_string_append _ | P_struct _ ),
      _ ) ->
      Error (l1, l2)

let diff_order (Ord_aux (o1, l1)) (Ord_aux (o2, l2)) =
  match (o1, o2) with Ord_inc, Ord_inc -> Ok () | Ord_dec, Ord_dec -> Ok () | (Ord_inc | Ord_dec), _ -> Error (l1, l2)

let rec diff_exp (E_aux (exp1, (l1, _)) as orig_exp1) (E_aux (exp2, (l2, _)) as orig_exp2) =
  match (exp1, exp2) with
  | E_block exps1, E_block exps2 -> diff_list (l1, l2) diff_exp exps1 exps2
  | E_block [exp1], _ -> diff_exp exp1 orig_exp2
  | _, E_block [exp2] -> diff_exp orig_exp1 exp2
  | E_id id1, E_id id2 -> diff_id id1 id2
  | E_lit lit1, E_lit lit2 -> diff_lit lit1 lit2
  | E_typ (typ1, exp1), E_typ (typ2, exp2) ->
      let* () = diff_exp exp1 exp2 in
      diff_typ typ1 typ2
  | E_app (f1, exps1), E_app (f2, exps2) ->
      let* () = diff_id f1 f2 in
      diff_list (l1, l2) diff_exp exps1 exps2
  | E_app_infix (lhs1, op1, rhs1), E_app_infix (lhs2, op2, rhs2) ->
      let* () = diff_id op1 op2 in
      let* () = diff_exp lhs1 lhs2 in
      diff_exp rhs1 rhs2
  | E_tuple exps1, E_tuple exps2 -> diff_list (l1, l2) diff_exp exps1 exps2
  | E_if (cond_exp1, then_exp1, else_exp1), E_if (cond_exp2, then_exp2, else_exp2) ->
      let* () = diff_exp cond_exp1 cond_exp2 in
      let* () = diff_exp then_exp1 then_exp2 in
      diff_exp else_exp1 else_exp2
  | E_loop (loop_type1, measure1, cond1, body_exp1), E_loop (loop_type2, measure2, cond2, body_exp2) ->
      let* () =
        match (loop_type1, loop_type2) with
        | While, While -> Ok ()
        | Until, Until -> Ok ()
        | (While | Until), _ -> Error (l1, l2)
      in
      let* () = diff_internal_loop_measure measure1 measure2 in
      let* () = diff_exp cond1 cond2 in
      diff_exp body_exp1 body_exp2
  | ( E_for (id1, from_exp1, to_exp1, by_exp1, order1, body_exp1),
      E_for (id2, from_exp2, to_exp2, by_exp2, order2, body_exp2) ) ->
      let* () = diff_id id1 id2 in
      let* () = diff_exp from_exp1 from_exp2 in
      let* () = diff_exp to_exp1 to_exp2 in
      let* () = diff_exp by_exp1 by_exp2 in
      let* () = diff_order order1 order2 in
      diff_exp body_exp1 body_exp2
  | E_vector exps1, E_vector exps2 -> diff_list (l1, l2) diff_exp exps1 exps2
  | E_vector_access (vec_exp1, ix_exp1), E_vector_access (vec_exp2, ix_exp2) ->
      let* () = diff_exp vec_exp1 vec_exp2 in
      diff_exp ix_exp1 ix_exp2
  | E_vector_subrange (vec_exp1, n_exp1, m_exp1), E_vector_subrange (vec_exp2, n_exp2, m_exp2) ->
      let* () = diff_exp vec_exp1 vec_exp2 in
      let* () = diff_exp n_exp1 n_exp2 in
      diff_exp m_exp1 m_exp2
  | E_vector_update (vec_exp1, ix_exp1, elem_exp1), E_vector_update (vec_exp2, ix_exp2, elem_exp2) ->
      let* () = diff_exp vec_exp1 vec_exp2 in
      let* () = diff_exp ix_exp1 ix_exp2 in
      diff_exp elem_exp1 elem_exp2
  | ( E_vector_update_subrange (vec_exp1, n_exp1, m_exp1, elem_exp1),
      E_vector_update_subrange (vec_exp2, n_exp2, m_exp2, elem_exp2) ) ->
      let* () = diff_exp vec_exp1 vec_exp2 in
      let* () = diff_exp n_exp1 n_exp2 in
      let* () = diff_exp m_exp1 m_exp2 in
      diff_exp elem_exp1 elem_exp2
  | E_vector_append (lhs1, rhs1), E_vector_append (lhs2, rhs2) ->
      let* () = diff_exp lhs1 lhs2 in
      diff_exp rhs1 rhs2
  | E_list exps1, E_list exps2 -> diff_list (l1, l2) diff_exp exps1 exps2
  | E_cons (hd_exp1, tl_exp1), E_cons (hd_exp2, tl_exp2) ->
      let* () = diff_exp hd_exp1 hd_exp2 in
      diff_exp tl_exp1 tl_exp2
  | E_struct fexps1, E_struct fexps2 -> diff_list (l1, l2) diff_fexp fexps1 fexps2
  | E_struct_update (exp1, fexps1), E_struct_update (exp2, fexps2) ->
      let* () = diff_exp exp1 exp2 in
      diff_list (l1, l2) diff_fexp fexps1 fexps2
  | E_field (exp1, id1), E_field (exp2, id2) ->
      let* () = diff_id id1 id2 in
      diff_exp exp1 exp2
  | E_match (exp1, pexps1), E_match (exp2, pexps2) ->
      let* () = diff_exp exp1 exp2 in
      diff_list (l1, l2) diff_pexp pexps1 pexps2
  | E_let (lb1, exp1), E_let (lb2, exp2) ->
      let* () = diff_letbind lb1 lb2 in
      diff_exp exp1 exp2
  | E_assign (lexp1, exp1), E_assign (lexp2, exp2) ->
      let* () = diff_lexp lexp1 lexp2 in
      diff_exp exp1 exp2
  | E_sizeof n1, E_sizeof n2 -> diff_nexp n1 n2
  | E_return exp1, E_return exp2 -> diff_exp exp1 exp2
  | E_exit exp1, E_exit exp2 -> diff_exp exp1 exp2
  | E_ref id1, E_ref id2 -> diff_id id1 id2
  | E_throw exp1, E_throw exp2 -> diff_exp exp1 exp2
  | E_try (exp1, pexps1), E_try (exp2, pexps2) ->
      let* () = diff_exp exp1 exp2 in
      diff_list (l1, l2) diff_pexp pexps1 pexps2
  | E_assert (exp1, msg_exp1), E_assert (exp2, msg_exp2) ->
      let* () = diff_exp exp1 exp2 in
      diff_exp msg_exp1 msg_exp2
  | E_var (lexp1, value_exp1, body_exp1), E_var (lexp2, value_exp2, body_exp2) ->
      let* () = diff_lexp lexp1 lexp2 in
      let* () = diff_exp value_exp1 value_exp2 in
      diff_exp body_exp1 body_exp2
  | E_internal_plet (pat1, value_exp1, body_exp1), E_internal_plet (pat2, value_exp2, body_exp2) ->
      let* () = diff_pat pat1 pat2 in
      let* () = diff_exp value_exp1 value_exp2 in
      diff_exp body_exp1 body_exp2
  | E_internal_return exp1, E_internal_return exp2 -> diff_exp exp1 exp2
  | E_internal_value v1, E_internal_value v2 -> if Value.eq_value v1 v2 then Ok () else Error (l1, l2)
  | E_internal_assume (nc1, exp1), E_internal_assume (nc2, exp2) ->
      let* () = diff_constraint nc1 nc2 in
      diff_exp exp1 exp2
  | E_constraint nc1, E_constraint nc2 -> diff_constraint nc1 nc2
  | ( ( E_block _ | E_id _ | E_lit _ | E_typ _ | E_app _ | E_app_infix _ | E_tuple _ | E_if _ | E_loop _ | E_for _
      | E_vector _ | E_vector_access _ | E_vector_subrange _ | E_vector_update _ | E_vector_update_subrange _
      | E_vector_append _ | E_list _ | E_cons _ | E_struct _ | E_struct_update _ | E_field _ | E_match _ | E_let _
      | E_assign _ | E_sizeof _ | E_return _ | E_exit _ | E_ref _ | E_throw _ | E_try _ | E_assert _ | E_var _
      | E_internal_plet _ | E_internal_return _ | E_internal_value _ | E_internal_assume _ | E_constraint _ ),
      _ ) ->
      Error (l1, l2)

and diff_internal_loop_measure (Measure_aux (m1, l1)) (Measure_aux (m2, l2)) =
  match (m1, m2) with
  | Measure_none, Measure_none -> Ok ()
  | Measure_some exp1, Measure_some exp2 -> diff_exp exp1 exp2
  | (Measure_none | Measure_some _), _ -> Error (l1, l2)

and diff_fexp (FE_aux (FE_fexp (id1, exp1), (l1, _))) (FE_aux (FE_fexp (id2, exp2), (l2, _))) =
  let* () = diff_id id1 id2 in
  diff_exp exp1 exp2

and diff_pexp (Pat_aux (pexp1, (l1, _))) (Pat_aux (pexp2, (l2, _))) =
  match (pexp1, pexp2) with
  | Pat_exp (pat1, exp1), Pat_exp (pat2, exp2) ->
      let* () = diff_pat pat1 pat2 in
      diff_exp exp1 exp2
  | Pat_when (pat1, guard1, exp1), Pat_when (pat2, guard2, exp2) ->
      let* () = diff_pat pat1 pat2 in
      let* () = diff_exp guard1 guard2 in
      diff_exp exp1 exp2
  | (Pat_exp _ | Pat_when _), _ -> Error (l1, l2)

and diff_lexp (LE_aux (lexp1, (l1, _))) (LE_aux (lexp2, (l2, _))) =
  match (lexp1, lexp2) with
  | LE_id id1, LE_id id2 -> diff_id id1 id2
  | LE_deref exp1, LE_deref exp2 -> diff_exp exp1 exp2
  | LE_app (f1, exps1), LE_app (f2, exps2) ->
      let* () = diff_id f1 f2 in
      diff_list (l1, l2) diff_exp exps1 exps2
  | LE_typ (typ1, id1), LE_typ (typ2, id2) ->
      let* () = diff_id id1 id2 in
      diff_typ typ1 typ2
  | LE_tuple lexps1, LE_tuple lexps2 -> diff_list (l1, l2) diff_lexp lexps1 lexps2
  | LE_vector_concat lexps1, LE_vector_concat lexps2 -> diff_list (l1, l2) diff_lexp lexps1 lexps2
  | LE_vector (lexp1, exp1), LE_vector (lexp2, exp2) ->
      let* () = diff_lexp lexp1 lexp2 in
      diff_exp exp1 exp2
  | LE_vector_range (lexp1, n_exp1, m_exp1), LE_vector_range (lexp2, n_exp2, m_exp2) ->
      let* () = diff_lexp lexp1 lexp2 in
      let* () = diff_exp n_exp1 n_exp2 in
      diff_exp m_exp1 m_exp2
  | LE_field (lexp1, id1), LE_field (lexp2, id2) ->
      let* () = diff_id id1 id2 in
      diff_lexp lexp1 lexp2
  | ( ( LE_id _ | LE_deref _ | LE_app _ | LE_typ _ | LE_tuple _ | LE_vector_concat _ | LE_vector _ | LE_vector_range _
      | LE_field _ ),
      _ ) ->
      Error (l1, l2)

and diff_letbind (LB_aux (LB_val (pat1, exp1), (l1, _))) (LB_aux (LB_val (pat2, exp2), (l2, _))) =
  let* () = diff_pat pat1 pat2 in
  diff_exp exp1 exp2

and diff_funcl (FCL_aux (FCL_funcl (f1, pexp1), _)) (FCL_aux (FCL_funcl (f2, pexp2), _)) =
  let* () = diff_id f1 f2 in
  diff_pexp pexp1 pexp2

let rec diff_mpat (MP_aux (mpat1, (l1, _))) (MP_aux (mpat2, (l2, _))) =
  match (mpat1, mpat2) with
  | MP_lit lit1, MP_lit lit2 -> diff_lit lit1 lit2
  | MP_as (pat1, id1), MP_as (pat2, id2) ->
      let* () = diff_id id1 id2 in
      diff_mpat pat1 pat2
  | MP_typ (pat1, typ1), MP_typ (pat2, typ2) ->
      let* () = diff_mpat pat1 pat2 in
      diff_typ typ1 typ2
  | MP_id id1, MP_id id2 -> diff_id id1 id2
  | MP_app (f1, pats1), MP_app (f2, pats2) ->
      let* () = diff_id f1 f2 in
      diff_list (l1, l2) diff_mpat pats1 pats2
  | MP_vector pats1, MP_vector pats2 -> diff_list (l1, l2) diff_mpat pats1 pats2
  | MP_vector_concat pats1, MP_vector_concat pats2 -> diff_list (l1, l2) diff_mpat pats1 pats2
  | MP_vector_subrange (id1, n1, m1), MP_vector_subrange (id2, n2, m2) ->
      let* () = diff_id id1 id2 in
      if Big_int.equal n1 n2 && Big_int.equal m1 m2 then Ok () else Error (l1, l2)
  | MP_tuple pats1, MP_tuple pats2 -> diff_list (l1, l2) diff_mpat pats1 pats2
  | MP_list pats1, MP_list pats2 -> diff_list (l1, l2) diff_mpat pats1 pats2
  | MP_cons (hd_pat1, tl_pat1), MP_cons (hd_pat2, tl_pat2) ->
      let* () = diff_mpat hd_pat1 hd_pat2 in
      diff_mpat tl_pat1 tl_pat2
  | MP_string_append pats1, MP_string_append pats2 -> diff_list (l1, l2) diff_mpat pats1 pats2
  | MP_struct fields1, MP_struct fields2 ->
      diff_list (l1, l2)
        (fun (id1, pat1) (id2, pat2) ->
          let* () = diff_id id1 id2 in
          diff_mpat pat1 pat2
        )
        fields1 fields2
  | ( ( MP_lit _ | MP_as _ | MP_typ _ | MP_id _ | MP_app _ | MP_vector _ | MP_vector_concat _ | MP_vector_subrange _
      | MP_tuple _ | MP_list _ | MP_cons _ | MP_string_append _ | MP_struct _ ),
      _ ) ->
      Error (l1, l2)

let diff_mpexp (MPat_aux (pexp1, (l1, _))) (MPat_aux (pexp2, (l2, _))) =
  match (pexp1, pexp2) with
  | MPat_pat pat1, MPat_pat pat2 -> diff_mpat pat1 pat2
  | MPat_when (pat1, guard1), MPat_when (pat2, guard2) ->
      let* () = diff_mpat pat1 pat2 in
      diff_exp guard1 guard2
  | (MPat_pat _ | MPat_when _), _ -> Error (l1, l2)

let diff_mapcl (MCL_aux (mcl1, (def_annot1, _))) (MCL_aux (mcl2, (def_annot2, _))) =
  match (mcl1, mcl2) with
  | MCL_bidir (mpexp_left1, mpexp_right1), MCL_bidir (mpexp_left2, mpexp_right2) ->
      let* () = diff_mpexp mpexp_left1 mpexp_left2 in
      diff_mpexp mpexp_right1 mpexp_right2
  | MCL_forwards (mpexp1, exp1), MCL_forwards (mpexp2, exp2) ->
      let* () = diff_mpexp mpexp1 mpexp2 in
      diff_exp exp1 exp2
  | MCL_backwards (mpexp1, exp1), MCL_backwards (mpexp2, exp2) ->
      let* () = diff_mpexp mpexp1 mpexp2 in
      diff_exp exp1 exp2
  | (MCL_bidir _ | MCL_forwards _ | MCL_backwards _), _ -> Error (def_annot1.loc, def_annot2.loc)

let diff_rec_opt (Rec_aux (r1, l1)) (Rec_aux (r2, l2)) =
  match (r1, r2) with
  | Rec_nonrec, Rec_nonrec -> Ok ()
  | Rec_rec, Rec_rec -> Ok ()
  | Rec_measure (pat1, exp1), Rec_measure (pat2, exp2) ->
      let* () = diff_pat pat1 pat2 in
      diff_exp exp1 exp2
  | (Rec_nonrec | Rec_rec | Rec_measure _), _ -> Error (l1, l2)

let diff_mapdef (MD_aux (MD_mapping (id1, t1, mapcls1), (l1, _))) (MD_aux (MD_mapping (id2, t2, mapcls2), (l2, _))) =
  let* () = diff_id id1 id2 in
  let* () = diff_tannot_opt t1 t2 in
  diff_list (l1, l2) diff_mapcl mapcls1 mapcls2

let diff_fundef (FD_aux (FD_function (r1, t1, funcls1), (l1, _))) (FD_aux (FD_function (r2, t2, funcls2), (l2, _))) =
  let* () = diff_rec_opt r1 r2 in
  let* () = diff_tannot_opt t1 t2 in
  diff_list (l1, l2) diff_funcl funcls1 funcls2

let diff_loop_measure (Loop (loop_type1, exp1)) (Loop (loop_type2, exp2)) =
  let* () =
    match (loop_type1, loop_type2) with
    | While, While -> Ok ()
    | Until, Until -> Ok ()
    | (While | Until), _ -> Error (exp_loc exp1, exp_loc exp2)
  in
  diff_exp exp1 exp2

let diff_scattered_def (SD_aux (sd1, (l1, _))) (SD_aux (sd2, (l2, _))) =
  match (sd1, sd2) with
  | SD_function (r1, t1, id1), SD_function (r2, t2, id2) ->
      let* () = diff_rec_opt r1 r2 in
      let* () = diff_tannot_opt t1 t2 in
      diff_id id1 id2
  | SD_funcl funcl1, SD_funcl funcl2 -> diff_funcl funcl1 funcl2
  | SD_variant (id1, typq1), SD_variant (id2, typq2) ->
      let* () = diff_id id1 id2 in
      diff_typquant typq1 typq2
  | SD_unioncl (id1, tu1), SD_unioncl (id2, tu2) ->
      let* () = diff_id id1 id2 in
      diff_type_union tu1 tu2
  | SD_mapping (id1, t1), SD_mapping (id2, t2) ->
      let* () = diff_id id1 id2 in
      diff_tannot_opt t1 t2
  | SD_mapcl (id1, mapcl1), SD_mapcl (id2, mapcl2) ->
      let* () = diff_id id1 id2 in
      diff_mapcl mapcl1 mapcl2
  | SD_enum id1, SD_enum id2 -> diff_id id1 id2
  | SD_enumcl (id1, member1), SD_enumcl (id2, member2) ->
      let* () = diff_id id1 id2 in
      diff_id member1 member2
  | SD_end id1, SD_end id2 -> diff_id id1 id2
  | ( ( SD_function _ | SD_funcl _ | SD_variant _ | SD_unioncl _ | SD_mapping _ | SD_mapcl _ | SD_enum _ | SD_enumcl _
      | SD_end _ ),
      _ ) ->
      Error (l1, l2)

let diff_extern err ext1 ext2 =
  if
    ext1.pure = ext2.pure
    && List.equal
         (fun (tgt1, str1) (tgt2, str2) -> String.equal tgt1 tgt2 && String.equal str1 str2)
         ext1.bindings ext2.bindings
  then Ok ()
  else Error err

let diff_outcome_spec (OV_aux (OV_outcome (id1, typschm1, vars1), l1)) (OV_aux (OV_outcome (id2, typschm2, vars2), l2))
    =
  let* () = diff_id id1 id2 in
  let* () = diff_typschm typschm1 typschm2 in
  diff_list (l1, l2) diff_kinded_id vars1 vars2

let diff_instantiation_spec (IN_aux (IN_id id1, _)) (IN_aux (IN_id id2, _)) = diff_id id1 id2

let diff_subst (IS_aux (subst1, l1)) (IS_aux (subst2, l2)) =
  match (subst1, subst2) with
  | IS_typ (v1, typ1), IS_typ (v2, typ2) ->
      let* () = diff_kid v1 v2 in
      diff_typ typ1 typ2
  | IS_id (lhs1, rhs1), IS_id (lhs2, rhs2) ->
      let* () = diff_id lhs1 lhs2 in
      diff_id rhs1 rhs2
  | (IS_typ _ | IS_id _), _ -> Error (l1, l2)

let diff_register (DEC_aux (DEC_reg (typ1, id1, value1), (l1, _))) (DEC_aux (DEC_reg (typ2, id2, value2), (l2, _))) =
  let* () = diff_id id1 id2 in
  let* () = diff_typ typ1 typ2 in
  diff_option (l1, l2) diff_exp value1 value2

let diff_val_spec (VS_aux (VS_val_spec (typschm1, id1, extern1), (l1, _)))
    (VS_aux (VS_val_spec (typschm2, id2, extern2), (l2, _))) =
  let* () = diff_id id1 id2 in
  let* () = diff_typschm typschm1 typschm2 in
  diff_option (l1, l2) (diff_extern (l1, l2)) extern1 extern2

let rec diff_def_aux l1 l2 def1 def2 =
  match (def1, def2) with
  | DEF_type td1, DEF_type td2 -> diff_type_def td1 td2
  | DEF_fundef fdef1, DEF_fundef fdef2 -> diff_fundef fdef1 fdef2
  | DEF_mapdef mdef1, DEF_mapdef mdef2 -> diff_mapdef mdef1 mdef2
  | DEF_impl funcl1, DEF_impl funcl2 -> diff_funcl funcl1 funcl2
  | DEF_let lb1, DEF_let lb2 -> diff_letbind lb1 lb2
  | DEF_val vs1, DEF_val vs2 -> diff_val_spec vs1 vs2
  | DEF_outcome (os1, defs1), DEF_outcome (os2, defs2) ->
      let* () = diff_outcome_spec os1 os2 in
      diff_list (l1, l2) diff_def defs1 defs2
  | DEF_instantiation (is1, substs1), DEF_instantiation (is2, substs2) ->
      let* () = diff_instantiation_spec is1 is2 in
      diff_list (l1, l2) diff_subst substs1 substs2
  | DEF_fixity (prec1, level1, id1), DEF_fixity (prec2, level2, id2) ->
      let* () =
        match (prec1, prec2) with
        | Infix, Infix -> Ok ()
        | InfixL, InfixL -> Ok ()
        | InfixR, InfixR -> Ok ()
        | (Infix | InfixL | InfixR), _ -> Error (l1, l2)
      in
      let* () = diff_id id1 id2 in
      if Big_int.equal level1 level2 then Ok () else Error (l1, l2)
  | DEF_overload (id1, ids1), DEF_overload (id2, ids2) ->
      let* () = diff_id id1 id2 in
      diff_list (l1, l2) diff_id ids1 ids2
  | DEF_default (DT_aux (DT_order o1, _)), DEF_default (DT_aux (DT_order o2, _)) -> diff_order o1 o2
  | DEF_scattered sd1, DEF_scattered sd2 -> diff_scattered_def sd1 sd2
  | DEF_measure (id1, pat1, exp1), DEF_measure (id2, pat2, exp2) ->
      let* () = diff_id id1 id2 in
      let* () = diff_pat pat1 pat2 in
      diff_exp exp1 exp2
  | DEF_loop_measures (id1, lms1), DEF_loop_measures (id2, lms2) ->
      let* () = diff_id id1 id2 in
      diff_list (l1, l2) diff_loop_measure lms1 lms2
  | DEF_register reg1, DEF_register reg2 -> diff_register reg1 reg2
  | DEF_internal_mutrec fdefs1, DEF_internal_mutrec fdefs2 -> diff_list (l1, l2) diff_fundef fdefs2 fdefs2
  | DEF_pragma (name1, arg1, _), DEF_pragma (name2, arg2, _) ->
      if String.equal name1 name2 && String.equal arg1 arg2 then Ok () else Error (l1, l2)
  | ( ( DEF_type _ | DEF_fundef _ | DEF_mapdef _ | DEF_impl _ | DEF_let _ | DEF_val _ | DEF_outcome _
      | DEF_instantiation _ | DEF_fixity _ | DEF_overload _ | DEF_default _ | DEF_scattered _ | DEF_measure _
      | DEF_loop_measures _ | DEF_register _ | DEF_internal_mutrec _ | DEF_pragma _ ),
      _ ) ->
      Error (l1, l2)

and diff_def (DEF_aux (def1, def_annot1)) (DEF_aux (def2, def_annot2)) =
  diff_def_aux def_annot1.loc def_annot2.loc def1 def2
