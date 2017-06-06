(**************************************************************************)
(*     Sail                                                               *)
(*                                                                        *)
(*  Copyright (c) 2013-2017                                               *)
(*    Kathyrn Gray                                                        *)
(*    Shaked Flur                                                         *)
(*    Stephen Kell                                                        *)
(*    Gabriel Kerneis                                                     *)
(*    Robert Norton-Wright                                                *)
(*    Christopher Pulte                                                   *)
(*    Peter Sewell                                                        *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(**************************************************************************)

open Big_int
open Ast
open Type_internal
open Spec_analysis
type typ = Type_internal.t
type 'a exp = 'a Ast.exp
type 'a emap = 'a Envmap.t
type envs = Type_check.envs
type 'a namemap = (typ * 'a exp) emap

type 'a rewriters = {
    rewrite_exp  : 'a rewriters -> (nexp_map * 'a namemap) option -> 'a exp -> 'a exp;
    rewrite_lexp : 'a rewriters -> (nexp_map * 'a namemap) option -> 'a lexp -> 'a lexp;
    rewrite_pat  : 'a rewriters -> (nexp_map * 'a namemap) option -> 'a pat -> 'a pat;
    rewrite_let  : 'a rewriters -> (nexp_map * 'a namemap) option -> 'a letbind -> 'a letbind;
    rewrite_fun  : 'a rewriters -> 'a fundef -> 'a fundef;
    rewrite_def  : 'a rewriters -> 'a def -> 'a def;
    rewrite_defs : 'a rewriters -> 'a defs -> 'a defs;
  }


let (>>) f g = fun x -> g(f(x))

let fresh_name_counter = ref 0

let fresh_name () =
  let current = !fresh_name_counter in
  let () = fresh_name_counter := (current + 1) in
  current
let reset_fresh_name_counter () =
  fresh_name_counter := 0

let get_effsum_annot (_,t) = match t with
  | Base (_,_,_,_,effs,_) -> effs
  | NoTyp -> failwith "no effect information" 
  | _ -> failwith "get_effsum_annot doesn't support Overload"

let get_localeff_annot (_,t) = match t with
  | Base (_,_,_,eff,_,_) -> eff
  | NoTyp -> failwith "no effect information" 
  | _ -> failwith "get_localeff_annot doesn't support Overload"

let get_type_annot (_,t) = match t with
  | Base((_,t),_,_,_,_,_) -> t
  | NoTyp -> failwith "no type information" 
  | _ -> failwith "get_type_annot doesn't support Overload"

let get_type (E_aux (_,a)) = get_type_annot a

let union_effs effs =
  List.fold_left (fun acc eff -> union_effects acc eff) pure_e effs

let get_effsum_exp (E_aux (_,a)) = get_effsum_annot a
let get_effsum_fpat (FP_aux (_,a)) = get_effsum_annot a
let get_effsum_lexp (LEXP_aux (_,a)) = get_effsum_annot a
let get_effsum_fexp (FE_aux (_,a)) = get_effsum_annot a
let get_effsum_fexps (FES_aux (FES_Fexps (fexps,_),_)) =
  union_effs (List.map get_effsum_fexp fexps)
let get_effsum_opt_default (Def_val_aux (_,a)) = get_effsum_annot a
let get_effsum_pexp (Pat_aux (_,a)) = get_effsum_annot a
let get_effsum_lb (LB_aux (_,a)) = get_effsum_annot a

let eff_union_exps es =
  union_effs (List.map get_effsum_exp es)

let fix_effsum_exp (E_aux (e,(l,annot))) = 
  let (Base (t,tag,nexps,eff,_,bounds)) = annot in
  let effsum = match e with
    | E_block es -> eff_union_exps es
    | E_nondet es -> eff_union_exps es
    | E_id _
    | E_lit _ -> pure_e
    | E_cast (_,e) -> get_effsum_exp e
    | E_app (_,es)
    | E_tuple es -> eff_union_exps es
    | E_app_infix (e1,_,e2) -> eff_union_exps [e1;e2]
    | E_if (e1,e2,e3) -> eff_union_exps [e1;e2;e3]
    | E_for (_,e1,e2,e3,_,e4) -> eff_union_exps [e1;e2;e3;e4]
    | E_vector es -> eff_union_exps es
    | E_vector_indexed (ies,opt_default) ->
       let (_,es) = List.split ies in
       union_effs (get_effsum_opt_default opt_default :: List.map get_effsum_exp es)
    | E_vector_access (e1,e2) -> eff_union_exps [e1;e2]
    | E_vector_subrange (e1,e2,e3) -> eff_union_exps [e1;e2;e3]
    | E_vector_update (e1,e2,e3) -> eff_union_exps [e1;e2;e3]
    | E_vector_update_subrange (e1,e2,e3,e4) -> eff_union_exps [e1;e2;e3;e4]
    | E_vector_append (e1,e2) -> eff_union_exps [e1;e2]
    | E_list es -> eff_union_exps es
    | E_cons (e1,e2) -> eff_union_exps [e1;e2]
    | E_record fexps -> get_effsum_fexps fexps
    | E_record_update(e,fexps) -> union_effs ((get_effsum_exp e)::[(get_effsum_fexps fexps)])
    | E_field (e,_) -> get_effsum_exp e
    | E_case (e,pexps) -> union_effs (get_effsum_exp e :: List.map get_effsum_pexp pexps)
    | E_let (lb,e) -> union_effs [get_effsum_lb lb;get_effsum_exp e]
    | E_assign (lexp,e) -> union_effs [get_effsum_lexp lexp;get_effsum_exp e]
    | E_exit e -> get_effsum_exp e
    | E_return e -> get_effsum_exp e
    | E_sizeof _ | E_sizeof_internal _ -> pure_e
    | E_assert (c,m) -> pure_e
    | E_comment _ | E_comment_struc _ -> pure_e
    | E_internal_cast (_,e) -> get_effsum_exp e
    | E_internal_exp _ -> pure_e
    | E_internal_exp_user _ -> pure_e
    | E_internal_let (lexp,e1,e2) -> union_effs [get_effsum_lexp lexp;
                                                 get_effsum_exp e1;get_effsum_exp e2]
    | E_internal_plet (_,e1,e2) -> union_effs [get_effsum_exp e1;get_effsum_exp e2]
    | E_internal_return e1 -> get_effsum_exp e1
  in
  E_aux (e,(l,(Base (t,tag,nexps,eff,union_effects eff effsum,bounds))))

let fix_effsum_lexp (LEXP_aux (lexp,(l,annot))) =
  let (Base (t,tag,nexps,eff,_,bounds)) = annot in
  let effsum = match lexp with
    | LEXP_id _ -> pure_e
    | LEXP_cast _ -> pure_e
    | LEXP_memory (_,es) -> eff_union_exps es
    | LEXP_vector (lexp,e) -> union_effs [get_effsum_lexp lexp;get_effsum_exp e]
    | LEXP_vector_range (lexp,e1,e2) -> union_effs [get_effsum_lexp lexp;get_effsum_exp e1;
                                                    get_effsum_exp e2]
    | LEXP_field (lexp,_) -> get_effsum_lexp lexp in
  LEXP_aux (lexp,(l,(Base (t,tag,nexps,eff,union_effects eff effsum,bounds))))

let fix_effsum_fexp (FE_aux (fexp,(l,annot))) =
  let (Base (t,tag,nexps,eff,_,bounds)) = annot in
  let effsum = match fexp with
    | FE_Fexp (_,e) -> get_effsum_exp e in
  FE_aux (fexp,(l,(Base (t,tag,nexps,eff,union_effects eff effsum,bounds))))

let fix_effsum_fexps fexps = fexps (* FES_aux have no effect information *)

let fix_effsum_opt_default (Def_val_aux (opt_default,(l,annot))) =
  let (Base (t,tag,nexps,eff,_,bounds)) = annot in
  let effsum = match opt_default with
    | Def_val_empty -> pure_e
    | Def_val_dec e -> get_effsum_exp e in
  Def_val_aux (opt_default,(l,(Base (t,tag,nexps,eff,union_effects eff effsum,bounds))))

let fix_effsum_pexp (Pat_aux (pexp,(l,annot))) =
  let (Base (t,tag,nexps,eff,_,bounds)) = annot in
  let effsum = match pexp with
    | Pat_exp (_,e) -> get_effsum_exp e in
  Pat_aux (pexp,(l,(Base (t,tag,nexps,eff,union_effects eff effsum,bounds))))

let fix_effsum_lb (LB_aux (lb,(l,annot))) =
  let (Base (t,tag,nexps,eff,_,bounds)) = annot in
  let effsum = match lb with
    | LB_val_explicit (_,_,e) -> get_effsum_exp e
    | LB_val_implicit (_,e) -> get_effsum_exp e in
  LB_aux (lb,(l,(Base (t,tag,nexps,eff,union_effects eff effsum,bounds))))

let effectful_effs {effect = Eset effs} =
  List.exists
    (fun (BE_aux (be,_)) ->
     match be with
     | BE_nondet | BE_unspec | BE_undef | BE_lset -> false
     | _ -> true
    ) effs

let effectful eaux = effectful_effs (get_effsum_exp eaux)

let updates_vars_effs {effect = Eset effs} =
  List.exists
    (fun (BE_aux (be,_)) ->
     match be with
     | BE_lset -> true
     | _ -> false
    ) effs

let updates_vars eaux = updates_vars_effs (get_effsum_exp eaux)


let rec partial_assoc (eq: 'a -> 'a -> bool) (v: 'a) (ls : ('a *'b) list ) : 'b option  = match ls with
  | [] -> None
  | (v1,v2)::ls -> if (eq v1 v) then Some v2 else partial_assoc eq v ls

let mk_atom_typ i = {t=Tapp("atom",[TA_nexp i])}

let rec rewrite_nexp_to_exp program_vars l nexp = 
  let rewrite n = rewrite_nexp_to_exp program_vars l n in
  let typ = mk_atom_typ nexp in
  let actual_rewrite_n nexp = 
    match nexp.nexp with
      | Nconst i -> E_aux (E_lit (L_aux (L_num (int_of_big_int i),l)), (l,simple_annot typ))
      | Nadd (n1,n2) -> E_aux (E_app_infix (rewrite n1,(Id_aux (Id "+",l)),rewrite n2),
                               (l, (tag_annot typ (External (Some "add")))))
      | Nmult (n1,n2) -> E_aux (E_app_infix (rewrite n1,(Id_aux (Id "*",l)),rewrite n2),
                                (l, tag_annot typ (External (Some "multiply"))))
      | Nsub (n1,n2) -> E_aux (E_app_infix (rewrite n1,(Id_aux (Id "-",l)),rewrite n2),
                               (l, tag_annot typ (External (Some "minus"))))
      | N2n (n, _) -> E_aux (E_app_infix (E_aux (E_lit (L_aux (L_num 2,l)), (l, simple_annot (mk_atom_typ n_two))),
                                          (Id_aux (Id "**",l)),
                                          rewrite n), (l, tag_annot typ (External (Some "power"))))
      | Npow(n,i) -> E_aux (E_app_infix 
                              (rewrite n, (Id_aux (Id "**",l)),
                               E_aux (E_lit (L_aux (L_num i,l)),
                                      (l, simple_annot (mk_atom_typ (mk_c_int i))))),
                            (l, tag_annot typ (External (Some "power"))))
      | Nneg(n) -> E_aux (E_app_infix (E_aux (E_lit (L_aux (L_num 0,l)), (l, simple_annot (mk_atom_typ n_zero))),
                                       (Id_aux (Id "-",l)),
                                       rewrite n),
                          (l, tag_annot typ (External (Some "minus"))))
      | Nvar v -> (*TODO these need to generate an error as it's a place where there's insufficient specification. 
                    But, for now I need to permit this to make power.sail compile, and most errors are in trap 
                    or vectors *)
              (*let _ = Printf.eprintf "unbound variable here %s\n" v in*) 
        E_aux (E_id (Id_aux (Id v,l)),(l,simple_annot typ))
      | _ -> raise (Reporting_basic.err_unreachable l ("rewrite_nexp given n that can't be rewritten: " ^ (n_to_string nexp))) in
  match program_vars with
    | None -> actual_rewrite_n nexp
    | Some program_vars ->
      (match partial_assoc nexp_eq_check nexp program_vars with
        | None -> actual_rewrite_n nexp
        | Some(None,ev) ->
          (*let _ = Printf.eprintf "var case of rewrite, %s\n" ev in*)
          E_aux (E_id (Id_aux (Id ev,l)), (l, simple_annot typ))
        | Some(Some f,ev) -> 
          E_aux (E_app ((Id_aux (Id f,l)), [ (E_aux (E_id (Id_aux (Id ev,l)), (l,simple_annot typ)))]),
                 (l, tag_annot typ (External (Some f)))))

let rec match_to_program_vars ns bounds =
  match ns with
    | [] -> []
    | n::ns -> match find_var_from_nexp n bounds with
        | None -> match_to_program_vars ns bounds
        | Some(augment,ev) -> 
          (*let _ = Printf.eprintf "adding n %s to program var %s\n" (n_to_string n) ev in*)
          (n,(augment,ev))::(match_to_program_vars ns bounds)

let explode s =
  let rec exp i l = if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []


let vector_string_to_bit_list l lit = 

  let hexchar_to_binlist = function
    | '0' -> ['0';'0';'0';'0']
    | '1' -> ['0';'0';'0';'1']
    | '2' -> ['0';'0';'1';'0']
    | '3' -> ['0';'0';'1';'1']
    | '4' -> ['0';'1';'0';'0']
    | '5' -> ['0';'1';'0';'1']
    | '6' -> ['0';'1';'1';'0']
    | '7' -> ['0';'1';'1';'1']
    | '8' -> ['1';'0';'0';'0']
    | '9' -> ['1';'0';'0';'1']
    | 'A' -> ['1';'0';'1';'0']
    | 'B' -> ['1';'0';'1';'1']
    | 'C' -> ['1';'1';'0';'0']
    | 'D' -> ['1';'1';'0';'1']
    | 'E' -> ['1';'1';'1';'0']
    | 'F' -> ['1';'1';'1';'1']
    | _ -> raise (Reporting_basic.err_unreachable l "hexchar_to_binlist given unrecognized character") in
  
  let s_bin = match lit with
    | L_hex s_hex -> List.flatten (List.map hexchar_to_binlist (explode (String.uppercase s_hex)))
    | L_bin s_bin -> explode s_bin
    | _ -> raise (Reporting_basic.err_unreachable l "s_bin given non vector literal") in

  List.map (function '0' -> L_aux (L_zero, Parse_ast.Generated l)
                   | '1' -> L_aux (L_one,Parse_ast.Generated l)
                   | _ -> raise (Reporting_basic.err_unreachable (Parse_ast.Generated l) "binary had non-zero or one")) s_bin

let rewrite_pat rewriters nmap (P_aux (pat,(l,annot))) =
  let rewrap p = P_aux (p,(l,annot)) in
  let rewrite = rewriters.rewrite_pat rewriters nmap in
  match pat with
  | P_lit (L_aux ((L_hex _ | L_bin _) as lit,_)) ->
    let ps =  List.map (fun p -> P_aux (P_lit p,(Parse_ast.Generated l,simple_annot {t = Tid "bit"})))
        (vector_string_to_bit_list l lit) in
    rewrap (P_vector ps)
  | P_lit _ | P_wild | P_id _ -> rewrap pat
  | P_as(pat,id) -> rewrap (P_as( rewrite pat, id))
  | P_typ(typ,pat) -> rewrite pat
  | P_app(id ,pats) -> rewrap (P_app(id, List.map rewrite pats))
  | P_record(fpats,_) ->
    rewrap (P_record(List.map (fun (FP_aux(FP_Fpat(id,pat),pannot)) -> FP_aux(FP_Fpat(id, rewrite pat), pannot)) fpats,
                     false))
  | P_vector pats -> rewrap (P_vector(List.map rewrite pats))
  | P_vector_indexed ipats -> rewrap (P_vector_indexed(List.map (fun (i,pat) -> (i, rewrite pat)) ipats))
  | P_vector_concat pats -> rewrap (P_vector_concat (List.map rewrite pats))
  | P_tup pats -> rewrap (P_tup (List.map rewrite pats))
  | P_list pats -> rewrap (P_list (List.map rewrite pats))

let rewrite_exp rewriters nmap (E_aux (exp,(l,annot))) = 
  let rewrap e = E_aux (e,(l,annot)) in
  let rewrite = rewriters.rewrite_exp rewriters nmap in
  match exp with
  | E_comment _ | E_comment_struc _ -> rewrap exp
  | E_block exps -> rewrap (E_block (List.map rewrite exps))
  | E_nondet exps -> rewrap (E_nondet (List.map rewrite exps))
  | E_lit (L_aux ((L_hex _ | L_bin _) as lit,_)) ->
    let es = List.map (fun p -> E_aux (E_lit p ,(Parse_ast.Generated l,simple_annot {t = Tid "bit"})))
        (vector_string_to_bit_list l lit) in
    rewrap (E_vector es)
  | E_id _ | E_lit _  -> rewrap exp
  | E_cast (typ, exp) -> rewrap (E_cast (typ, rewrite exp))
  | E_app (id,exps) -> rewrap (E_app (id,List.map rewrite exps))
  | E_app_infix(el,id,er) -> rewrap (E_app_infix(rewrite el,id,rewrite er))
  | E_tuple exps -> rewrap (E_tuple (List.map rewrite exps))
  | E_if (c,t,e) -> rewrap (E_if (rewrite c,rewrite t, rewrite e))
  | E_for (id, e1, e2, e3, o, body) ->
    rewrap (E_for (id, rewrite e1, rewrite e2, rewrite e3, o, rewrite body))
  | E_vector exps -> rewrap (E_vector (List.map rewrite exps))
  | E_vector_indexed (exps,(Def_val_aux(default,dannot))) ->
    let def = match default with
      | Def_val_empty -> default
      | Def_val_dec e -> Def_val_dec (rewrite e) in
    rewrap (E_vector_indexed (List.map (fun (i,e) -> (i, rewrite e)) exps, Def_val_aux(def,dannot)))
  | E_vector_access (vec,index) -> rewrap (E_vector_access (rewrite vec,rewrite index))
  | E_vector_subrange (vec,i1,i2) ->
    rewrap (E_vector_subrange (rewrite vec,rewrite i1,rewrite i2))
  | E_vector_update (vec,index,new_v) -> 
    rewrap (E_vector_update (rewrite vec,rewrite index,rewrite new_v))
  | E_vector_update_subrange (vec,i1,i2,new_v) ->
    rewrap (E_vector_update_subrange (rewrite vec,rewrite i1,rewrite i2,rewrite new_v))
  | E_vector_append (v1,v2) -> rewrap (E_vector_append (rewrite v1,rewrite v2))
  | E_list exps -> rewrap (E_list (List.map rewrite exps)) 
  | E_cons(h,t) -> rewrap (E_cons (rewrite h,rewrite t))
  | E_record (FES_aux (FES_Fexps(fexps, bool),fannot)) -> 
    rewrap (E_record 
              (FES_aux (FES_Fexps 
                          (List.map (fun (FE_aux(FE_Fexp(id,e),fannot)) -> 
                               FE_aux(FE_Fexp(id,rewrite e),fannot)) fexps, bool), fannot)))
  | E_record_update (re,(FES_aux (FES_Fexps(fexps, bool),fannot))) ->
    rewrap (E_record_update ((rewrite re),
                             (FES_aux (FES_Fexps 
                                         (List.map (fun (FE_aux(FE_Fexp(id,e),fannot)) -> 
                                              FE_aux(FE_Fexp(id,rewrite e),fannot)) fexps, bool), fannot))))
  | E_field(exp,id) -> rewrap (E_field(rewrite exp,id))
  | E_case (exp ,pexps) -> 
    rewrap (E_case (rewrite exp,
                    (List.map 
                       (fun (Pat_aux (Pat_exp(p,e),pannot)) -> 
                          Pat_aux (Pat_exp(rewriters.rewrite_pat rewriters nmap p,rewrite e),pannot)) pexps)))
  | E_let (letbind,body) -> rewrap (E_let(rewriters.rewrite_let rewriters nmap letbind,rewrite body))
  | E_assign (lexp,exp) -> rewrap (E_assign(rewriters.rewrite_lexp rewriters nmap lexp,rewrite exp))
  | E_sizeof n -> rewrap (E_sizeof n)
  | E_exit e -> rewrap (E_exit (rewrite e))
  | E_return e -> rewrap (E_return (rewrite e))
  | E_assert(e1,e2) -> rewrap (E_assert(rewrite e1,rewrite e2))
  | E_internal_cast ((l,casted_annot),exp) -> 
    let new_exp = rewrite exp in
    (*let _ = Printf.eprintf "Removing an internal_cast with %s\n" (tannot_to_string casted_annot) in*)
    (match casted_annot,exp with
     | Base((_,t),_,_,_,_,_),E_aux(ec,(ecl,Base((_,exp_t),_,_,_,_,_))) ->
       (*let _ = Printf.eprintf "Considering removing an internal cast where the two types are %s and %s\n" 
         (t_to_string t) (t_to_string exp_t) in*)
       (match t.t,exp_t.t with
        (*TODO should pass d_env into here so that I can look at the abbreviations if there are any here*)
        | Tapp("vector",[TA_nexp n1;TA_nexp nw1;TA_ord o1;_]),
          Tapp("vector",[TA_nexp n2;TA_nexp nw2;TA_ord o2;_]) 
        | Tapp("vector",[TA_nexp n1;TA_nexp nw1;TA_ord o1;_]),
          Tapp("reg",[TA_typ {t=(Tapp("vector",[TA_nexp n2; TA_nexp nw2; TA_ord o2;_]))}]) ->
          (match n1.nexp with
           | Nconst i1 -> if nexp_eq n1 n2 then new_exp else rewrap (E_cast (t_to_typ t,new_exp))
           | _ -> (match o1.order with
               | Odec -> 
                 (*let _ = Printf.eprintf "Considering removing a cast or not: %s %s, %b\n" 
                     (n_to_string nw1) (n_to_string n1) (nexp_one_more_than nw1 n1) in*)
                 rewrap (E_cast (Typ_aux (Typ_var (Kid_aux((Var "length"),Parse_ast.Generated l)),
                                          Parse_ast.Generated l),new_exp))
               | _ -> new_exp))
        | _ -> new_exp)
     | Base((_,t),_,_,_,_,_),_ ->
       (*let _ = Printf.eprintf "Considering removing an internal cast where the remaining type is %s\n%!"
            (t_to_string t) in*)
       (match t.t with
        | Tapp("vector",[TA_nexp n1;TA_nexp nw1;TA_ord o1;_]) ->
          (match o1.order with
           | Odec -> 
             let _ = Printf.eprintf "Considering removing a cast or not: %s %s, %b\n" 
                 (n_to_string nw1) (n_to_string n1) (nexp_one_more_than nw1 n1) in
             rewrap (E_cast (Typ_aux (Typ_var (Kid_aux((Var "length"), Parse_ast.Generated l)),
                                      Parse_ast.Generated l), new_exp))
           | _ -> new_exp)
        | _ -> new_exp)
     | _ -> (*let _ = Printf.eprintf "Not a base match?\n" in*) new_exp)
  | E_internal_exp (l,impl) ->
    (match impl with
     | Base((_,t),_,_,_,_,bounds) ->
       (*let _ = Printf.eprintf "Rewriting internal expression, with type %s, and bounds %s\n" 
         (t_to_string t) (bounds_to_string bounds) in*)
       let bounds = match nmap with | None -> bounds | Some (nm,_) -> add_map_to_bounds nm bounds in
       (*let _ = Printf.eprintf "Bounds after looking at nmap %s\n" (bounds_to_string bounds) in*)
       (match t.t with
        (*Old case; should possibly be removed*)
        | Tapp("register",[TA_typ {t= Tapp("vector",[ _; TA_nexp r;_;_])}])
        | Tapp("vector", [_;TA_nexp r;_;_])
        | Tabbrev(_, {t=Tapp("vector",[_;TA_nexp r;_;_])}) ->
          (*let _ = Printf.eprintf "vector case with %s, bounds are %s\n" 
                (n_to_string r) (bounds_to_string bounds) in*)
          let nexps = expand_nexp r in
          (match (match_to_program_vars nexps bounds) with
           | [] -> rewrite_nexp_to_exp None l r
           | map -> rewrite_nexp_to_exp (Some map) l r)
        | Tapp("implicit", [TA_nexp i]) ->
          (*let _ = Printf.eprintf "Implicit case with %s\n" (n_to_string i) in*)
          let nexps = expand_nexp i in
          (match (match_to_program_vars nexps bounds) with
           | [] -> rewrite_nexp_to_exp None l i
           | map -> rewrite_nexp_to_exp (Some map) l i)
        | _ -> 
          raise (Reporting_basic.err_unreachable l 
                   ("Internal_exp given unexpected types " ^ (t_to_string t))))
     | _ -> raise (Reporting_basic.err_unreachable l ("Internal_exp given none Base annot")))
  | E_sizeof_internal (l,impl) ->
    (match impl with
     | Base((_,t),_,_,_,_,bounds) ->
       let bounds = match nmap with | None -> bounds | Some (nm,_) -> add_map_to_bounds nm bounds in
       (match t.t with
        | Tapp("atom",[TA_nexp n]) ->
          let nexps = expand_nexp n in
          (*let _ = Printf.eprintf "Removing sizeof_internal with type %s\n" (t_to_string t) in*)
          (match (match_to_program_vars nexps bounds) with
           | [] -> rewrite_nexp_to_exp None l n
           | map -> rewrite_nexp_to_exp (Some map) l n)
        | _ -> raise (Reporting_basic.err_unreachable l ("Sizeof internal had non-atom type " ^ (t_to_string t))))
     | _ -> raise (Reporting_basic.err_unreachable l ("Sizeof internal had none base annot")))
  | E_internal_exp_user ((l,user_spec),(_,impl)) -> 
    (match (user_spec,impl) with
     | (Base((_,tu),_,_,_,_,_), Base((_,ti),_,_,_,_,bounds)) ->
       (*let _ = Printf.eprintf "E_interal_user getting rewritten two types are %s and %s\n"
            (t_to_string tu) (t_to_string ti) in*)
       let bounds =  match nmap with | None -> bounds | Some (nm,_) -> add_map_to_bounds nm bounds in
       (match (tu.t,ti.t) with
        | (Tapp("implicit", [TA_nexp u]),Tapp("implicit",[TA_nexp i])) ->
          (*let _ = Printf.eprintf "Implicit case with %s\n" (n_to_string i) in*)
          let nexps = expand_nexp i in
          (match (match_to_program_vars nexps bounds) with
           | [] -> rewrite_nexp_to_exp None l i
           (*add u to program_vars env; for now it will work out properly by accident*)
           | map -> rewrite_nexp_to_exp (Some map) l i)
        | _ -> 
          raise (Reporting_basic.err_unreachable l 
                   ("Internal_exp_user given unexpected types " ^ (t_to_string tu) ^ ", " ^ (t_to_string ti))))
     | _ -> raise (Reporting_basic.err_unreachable l ("Internal_exp_user given none Base annot")))
  | E_internal_let _ -> raise (Reporting_basic.err_unreachable l "Internal let found before it should have been introduced")
  | E_internal_return _ -> raise (Reporting_basic.err_unreachable l "Internal return found before it should have been introduced")
  | E_internal_plet _ -> raise (Reporting_basic.err_unreachable l " Internal plet found before it should have been introduced")
                           
let rewrite_let rewriters map (LB_aux(letbind,(l,annot))) =
  let local_map = get_map_tannot annot in
  let map =
    match map,local_map with
    | None,None -> None
    | None,Some m -> Some(m, Envmap.empty)
    | Some(m,s), None -> Some(m,s)
    | Some(m,s), Some m' -> match merge_option_maps (Some m) local_map with
      | None -> Some(m,s) (*Shouldn't happen*)
      | Some new_m -> Some(new_m,s) in
  match letbind with
  | LB_val_explicit (typschm, pat,exp) ->
    LB_aux(LB_val_explicit (typschm,rewriters.rewrite_pat rewriters map pat,
                            rewriters.rewrite_exp rewriters map exp),(l,annot))
  | LB_val_implicit ( pat, exp) ->
    LB_aux(LB_val_implicit (rewriters.rewrite_pat rewriters map pat,
                            rewriters.rewrite_exp rewriters map exp),(l,annot))

let rewrite_lexp rewriters map (LEXP_aux(lexp,(l,annot))) = 
  let rewrap le = LEXP_aux(le,(l,annot)) in
  match lexp with
  | LEXP_id _ | LEXP_cast _ -> rewrap lexp
  | LEXP_tup tupls -> rewrap (LEXP_tup (List.map (rewriters.rewrite_lexp rewriters map) tupls))
  | LEXP_memory (id,exps) -> rewrap (LEXP_memory(id,List.map (rewriters.rewrite_exp rewriters map) exps))
  | LEXP_vector (lexp,exp) ->
    rewrap (LEXP_vector (rewriters.rewrite_lexp rewriters map lexp,rewriters.rewrite_exp rewriters map exp))
  | LEXP_vector_range (lexp,exp1,exp2) -> 
    rewrap (LEXP_vector_range (rewriters.rewrite_lexp rewriters map lexp,
                               rewriters.rewrite_exp rewriters map exp1,
                               rewriters.rewrite_exp rewriters map exp2))
  | LEXP_field (lexp,id) -> rewrap (LEXP_field (rewriters.rewrite_lexp rewriters map lexp,id))

let rewrite_fun rewriters (FD_aux (FD_function(recopt,tannotopt,effectopt,funcls),(l,fdannot))) = 
  let rewrite_funcl (FCL_aux (FCL_Funcl(id,pat,exp),(l,annot))) =
    let _ = reset_fresh_name_counter () in
    (*let _ = Printf.eprintf "Rewriting function %s, pattern %s\n" 
      (match id with (Id_aux (Id i,_)) -> i) (Pretty_print.pat_to_string pat) in*)
  let map = get_map_tannot fdannot in
  let map =
    match map with
    | None -> None
    | Some m -> Some(m, Envmap.empty) in
  (FCL_aux (FCL_Funcl (id,rewriters.rewrite_pat rewriters map pat,
                         rewriters.rewrite_exp rewriters map exp),(l,annot))) 
  in FD_aux (FD_function(recopt,tannotopt,effectopt,List.map rewrite_funcl funcls),(l,fdannot))

let rewrite_def rewriters d = match d with
  | DEF_type _ | DEF_kind _ | DEF_spec _ | DEF_default _ | DEF_reg_dec _ | DEF_comm _ -> d
  | DEF_fundef fdef -> DEF_fundef (rewriters.rewrite_fun rewriters fdef)
  | DEF_val letbind -> DEF_val (rewriters.rewrite_let rewriters None letbind)
  | DEF_scattered _ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "DEF_scattered survived to rewritter")

let rewrite_defs_base rewriters (Defs defs) = 
  let rec rewrite ds = match ds with
    | [] -> []
    | d::ds -> (rewriters.rewrite_def rewriters d)::(rewrite ds) in
  Defs (rewrite defs)
    
let rewrite_defs (Defs defs) = rewrite_defs_base
    {rewrite_exp = rewrite_exp;
     rewrite_pat = rewrite_pat;
     rewrite_let = rewrite_let;
     rewrite_lexp = rewrite_lexp;
     rewrite_fun = rewrite_fun;
     rewrite_def = rewrite_def;
     rewrite_defs = rewrite_defs_base} (Defs defs)


let rec introduced_variables (E_aux (exp,(l,annot))) =
  match exp with
  | E_cast (typ, exp) -> introduced_variables exp
  | E_if (c,t,e) -> Envmap.intersect (introduced_variables t) (introduced_variables e)
  | E_assign (lexp,exp) -> introduced_vars_le lexp exp
  | _ -> Envmap.empty

and introduced_vars_le (LEXP_aux(lexp,(l,annot))) exp = 
  match lexp with
  | LEXP_id (Id_aux (Id id,_))  | LEXP_cast(_,(Id_aux (Id id,_))) ->
    (match annot with
     | Base((_,t),Emp_intro,_,_,_,_) ->
       Envmap.insert Envmap.empty (id,(t,exp))
     | _ -> Envmap.empty)
  | _ -> Envmap.empty

type ('a,'pat,'pat_aux,'fpat,'fpat_aux) pat_alg =
  { p_lit            : lit -> 'pat_aux
  ; p_wild           : 'pat_aux
  ; p_as             : 'pat * id -> 'pat_aux
  ; p_typ            : Ast.typ * 'pat -> 'pat_aux
  ; p_id             : id -> 'pat_aux
  ; p_app            : id * 'pat list -> 'pat_aux
  ; p_record         : 'fpat list * bool -> 'pat_aux
  ; p_vector         : 'pat list -> 'pat_aux
  ; p_vector_indexed : (int * 'pat) list -> 'pat_aux
  ; p_vector_concat  : 'pat list -> 'pat_aux
  ; p_tup            : 'pat list -> 'pat_aux
  ; p_list           : 'pat list -> 'pat_aux
  ; p_aux            : 'pat_aux * 'a annot -> 'pat
  ; fP_aux           : 'fpat_aux * 'a annot -> 'fpat
  ; fP_Fpat          : id * 'pat -> 'fpat_aux
  }

let rec fold_pat_aux (alg : ('a,'pat,'pat_aux,'fpat,'fpat_aux) pat_alg) : 'a pat_aux -> 'pat_aux =
  function
  | P_lit lit           -> alg.p_lit lit
  | P_wild              -> alg.p_wild
  | P_id id             -> alg.p_id id
  | P_as (p,id)         -> alg.p_as (fold_pat alg p,id)
  | P_typ (typ,p)       -> alg.p_typ (typ,fold_pat alg p)
  | P_app (id,ps)       -> alg.p_app (id,List.map (fold_pat alg) ps)
  | P_record (ps,b)     -> alg.p_record (List.map (fold_fpat alg) ps, b)
  | P_vector ps         -> alg.p_vector (List.map (fold_pat alg) ps)
  | P_vector_indexed ps -> alg.p_vector_indexed (List.map (fun (i,p) -> (i, fold_pat alg p)) ps)
  | P_vector_concat ps  -> alg.p_vector_concat (List.map (fold_pat alg) ps)
  | P_tup ps            -> alg.p_tup (List.map (fold_pat alg) ps)
  | P_list ps           -> alg.p_list (List.map (fold_pat alg) ps)


and fold_pat (alg : ('a,'pat,'pat_aux,'fpat,'fpat_aux) pat_alg) : 'a pat -> 'pat =
  function
  | P_aux (pat,annot)   -> alg.p_aux (fold_pat_aux alg pat,annot)
and fold_fpat_aux (alg : ('a,'pat,'pat_aux,'fpat,'fpat_aux) pat_alg) : 'a fpat_aux -> 'fpat_aux =
  function
  | FP_Fpat (id,pat)    -> alg.fP_Fpat (id,fold_pat alg pat)
and fold_fpat (alg : ('a,'pat,'pat_aux,'fpat,'fpat_aux) pat_alg) : 'a fpat -> 'fpat =
  function
  | FP_aux (fpat,annot) -> alg.fP_aux (fold_fpat_aux alg fpat,annot)
                                      
(* identity fold from term alg to term alg *)
let id_pat_alg : ('a,'a pat, 'a pat_aux, 'a fpat, 'a fpat_aux) pat_alg = 
  { p_lit            = (fun lit -> P_lit lit)
  ; p_wild           = P_wild
  ; p_as             = (fun (pat,id) -> P_as (pat,id))
  ; p_typ            = (fun (typ,pat) -> P_typ (typ,pat))
  ; p_id             = (fun id -> P_id id)
  ; p_app            = (fun (id,ps) -> P_app (id,ps))
  ; p_record         = (fun (ps,b) -> P_record (ps,b))
  ; p_vector         = (fun ps -> P_vector ps)
  ; p_vector_indexed = (fun ps -> P_vector_indexed ps)
  ; p_vector_concat  = (fun ps -> P_vector_concat ps)
  ; p_tup            = (fun ps -> P_tup ps)
  ; p_list           = (fun ps -> P_list ps)
  ; p_aux            = (fun (pat,annot) -> P_aux (pat,annot))
  ; fP_aux           = (fun (fpat,annot) -> FP_aux (fpat,annot))
  ; fP_Fpat          = (fun (id,pat) -> FP_Fpat (id,pat))
  }
  
type ('a,'exp,'exp_aux,'lexp,'lexp_aux,'fexp,'fexp_aux,'fexps,'fexps_aux,
      'opt_default_aux,'opt_default,'pexp,'pexp_aux,'letbind_aux,'letbind,
      'pat,'pat_aux,'fpat,'fpat_aux) exp_alg = 
  { e_block                  : 'exp list -> 'exp_aux
  ; e_nondet                 : 'exp list -> 'exp_aux
  ; e_id                     : id -> 'exp_aux
  ; e_lit                    : lit -> 'exp_aux
  ; e_cast                   : Ast.typ * 'exp -> 'exp_aux
  ; e_app                    : id * 'exp list -> 'exp_aux
  ; e_app_infix              : 'exp * id * 'exp -> 'exp_aux
  ; e_tuple                  : 'exp list -> 'exp_aux
  ; e_if                     : 'exp * 'exp * 'exp -> 'exp_aux
  ; e_for                    : id * 'exp * 'exp * 'exp * Ast.order * 'exp -> 'exp_aux
  ; e_vector                 : 'exp list -> 'exp_aux
  ; e_vector_indexed         : (int * 'exp) list * 'opt_default -> 'exp_aux
  ; e_vector_access          : 'exp * 'exp -> 'exp_aux
  ; e_vector_subrange        : 'exp * 'exp * 'exp -> 'exp_aux
  ; e_vector_update          : 'exp * 'exp * 'exp -> 'exp_aux
  ; e_vector_update_subrange : 'exp * 'exp * 'exp * 'exp -> 'exp_aux
  ; e_vector_append          : 'exp * 'exp -> 'exp_aux
  ; e_list                   : 'exp list -> 'exp_aux
  ; e_cons                   : 'exp * 'exp -> 'exp_aux
  ; e_record                 : 'fexps -> 'exp_aux
  ; e_record_update          : 'exp * 'fexps -> 'exp_aux
  ; e_field                  : 'exp * id -> 'exp_aux
  ; e_case                   : 'exp * 'pexp list -> 'exp_aux
  ; e_let                    : 'letbind * 'exp -> 'exp_aux
  ; e_assign                 : 'lexp * 'exp -> 'exp_aux
  ; e_exit                   : 'exp -> 'exp_aux
  ; e_return                 : 'exp -> 'exp_aux
  ; e_assert                 : 'exp * 'exp -> 'exp_aux
  ; e_internal_cast          : 'a annot * 'exp -> 'exp_aux
  ; e_internal_exp           : 'a annot -> 'exp_aux
  ; e_internal_exp_user      : 'a annot * 'a annot -> 'exp_aux
  ; e_internal_let           : 'lexp * 'exp * 'exp -> 'exp_aux
  ; e_internal_plet          : 'pat * 'exp * 'exp -> 'exp_aux
  ; e_internal_return        : 'exp -> 'exp_aux
  ; e_aux                    : 'exp_aux * 'a annot -> 'exp
  ; lEXP_id                  : id -> 'lexp_aux
  ; lEXP_memory              : id * 'exp list -> 'lexp_aux
  ; lEXP_cast                : Ast.typ * id -> 'lexp_aux
  ; lEXP_tup                 : 'lexp list -> 'lexp_aux
  ; lEXP_vector              : 'lexp * 'exp -> 'lexp_aux
  ; lEXP_vector_range        : 'lexp * 'exp * 'exp -> 'lexp_aux
  ; lEXP_field               : 'lexp * id -> 'lexp_aux
  ; lEXP_aux                 : 'lexp_aux * 'a annot -> 'lexp
  ; fE_Fexp                  : id * 'exp -> 'fexp_aux
  ; fE_aux                   : 'fexp_aux * 'a annot -> 'fexp
  ; fES_Fexps                : 'fexp list * bool -> 'fexps_aux
  ; fES_aux                  : 'fexps_aux * 'a annot -> 'fexps
  ; def_val_empty            : 'opt_default_aux
  ; def_val_dec              : 'exp -> 'opt_default_aux
  ; def_val_aux              : 'opt_default_aux * 'a annot -> 'opt_default
  ; pat_exp                  : 'pat * 'exp -> 'pexp_aux
  ; pat_aux                  : 'pexp_aux * 'a annot -> 'pexp
  ; lB_val_explicit          : typschm * 'pat * 'exp -> 'letbind_aux
  ; lB_val_implicit          : 'pat * 'exp -> 'letbind_aux
  ; lB_aux                   : 'letbind_aux * 'a annot -> 'letbind
  ; pat_alg                  : ('a,'pat,'pat_aux,'fpat,'fpat_aux) pat_alg
  }
    
let rec fold_exp_aux alg = function
  | E_block es -> alg.e_block (List.map (fold_exp alg) es)
  | E_nondet es -> alg.e_nondet (List.map (fold_exp alg) es)
  | E_id id -> alg.e_id id
  | E_lit lit -> alg.e_lit lit
  | E_cast (typ,e) -> alg.e_cast (typ, fold_exp alg e)
  | E_app (id,es) -> alg.e_app (id, List.map (fold_exp alg) es)
  | E_app_infix (e1,id,e2) -> alg.e_app_infix (fold_exp alg e1, id, fold_exp alg e2)
  | E_tuple es -> alg.e_tuple (List.map (fold_exp alg) es)
  | E_if (e1,e2,e3) -> alg.e_if (fold_exp alg e1, fold_exp alg e2, fold_exp alg e3)
  | E_for (id,e1,e2,e3,order,e4) ->
     alg.e_for (id,fold_exp alg e1, fold_exp alg e2, fold_exp alg e3, order, fold_exp alg e4)
  | E_vector es -> alg.e_vector (List.map (fold_exp alg) es)
  | E_vector_indexed (es,opt) ->
     alg.e_vector_indexed (List.map (fun (id,e) -> (id,fold_exp alg e)) es, fold_opt_default alg opt)
  | E_vector_access (e1,e2) -> alg.e_vector_access (fold_exp alg e1, fold_exp alg e2)
  | E_vector_subrange (e1,e2,e3) ->
     alg.e_vector_subrange (fold_exp alg e1, fold_exp alg e2, fold_exp alg e3)
  | E_vector_update (e1,e2,e3) ->
     alg.e_vector_update (fold_exp alg e1, fold_exp alg e2, fold_exp alg e3)
  | E_vector_update_subrange (e1,e2,e3,e4) ->
     alg.e_vector_update_subrange (fold_exp alg e1,fold_exp alg e2, fold_exp alg e3, fold_exp alg e4)
  | E_vector_append (e1,e2) -> alg.e_vector_append (fold_exp alg e1, fold_exp alg e2)
  | E_list es -> alg.e_list (List.map (fold_exp alg) es)
  | E_cons (e1,e2) -> alg.e_cons (fold_exp alg e1, fold_exp alg e2)
  | E_record fexps -> alg.e_record (fold_fexps alg fexps)
  | E_record_update (e,fexps) -> alg.e_record_update (fold_exp alg e, fold_fexps alg fexps)
  | E_field (e,id) -> alg.e_field (fold_exp alg e, id)
  | E_case (e,pexps) -> alg.e_case (fold_exp alg e, List.map (fold_pexp alg) pexps)
  | E_let (letbind,e) -> alg.e_let (fold_letbind alg letbind, fold_exp alg e)
  | E_assign (lexp,e) -> alg.e_assign (fold_lexp alg lexp, fold_exp alg e)
  | E_exit e -> alg.e_exit (fold_exp alg e)
  | E_return e -> alg.e_return (fold_exp alg e)
  | E_assert(e1,e2) -> alg.e_assert (fold_exp alg e1, fold_exp alg e2)
  | E_internal_cast (annot,e) -> alg.e_internal_cast (annot, fold_exp alg e)
  | E_internal_exp annot -> alg.e_internal_exp annot
  | E_internal_exp_user (annot1,annot2) -> alg.e_internal_exp_user (annot1,annot2)
  | E_internal_let (lexp,e1,e2) ->
     alg.e_internal_let (fold_lexp alg lexp, fold_exp alg e1, fold_exp alg e2)
  | E_internal_plet (pat,e1,e2) ->
     alg.e_internal_plet (fold_pat alg.pat_alg pat, fold_exp alg e1, fold_exp alg e2)
  | E_internal_return e -> alg.e_internal_return (fold_exp alg e)
and fold_exp alg (E_aux (exp_aux,annot)) = alg.e_aux (fold_exp_aux alg exp_aux, annot)
and fold_lexp_aux alg = function
  | LEXP_id id -> alg.lEXP_id id
  | LEXP_memory (id,es) -> alg.lEXP_memory (id, List.map (fold_exp alg) es)
  | LEXP_cast (typ,id) -> alg.lEXP_cast (typ,id)
  | LEXP_vector (lexp,e) -> alg.lEXP_vector (fold_lexp alg lexp, fold_exp alg e)
  | LEXP_vector_range (lexp,e1,e2) ->
     alg.lEXP_vector_range (fold_lexp alg lexp, fold_exp alg e1, fold_exp alg e2)
  | LEXP_field (lexp,id) -> alg.lEXP_field (fold_lexp alg lexp, id)
  | LEXP_tup es -> alg.lEXP_tup (List.map (fold_lexp alg) es)
and fold_lexp alg (LEXP_aux (lexp_aux,annot)) =
  alg.lEXP_aux (fold_lexp_aux alg lexp_aux, annot)
and fold_fexp_aux alg (FE_Fexp (id,e)) = alg.fE_Fexp (id, fold_exp alg e)
and fold_fexp alg (FE_aux (fexp_aux,annot)) = alg.fE_aux (fold_fexp_aux alg fexp_aux,annot)
and fold_fexps_aux alg (FES_Fexps (fexps,b)) = alg.fES_Fexps (List.map (fold_fexp alg) fexps, b)
and fold_fexps alg (FES_aux (fexps_aux,annot)) = alg.fES_aux (fold_fexps_aux alg fexps_aux, annot)
and fold_opt_default_aux alg = function
  | Def_val_empty -> alg.def_val_empty
  | Def_val_dec e -> alg.def_val_dec (fold_exp alg e)
and fold_opt_default alg (Def_val_aux (opt_default_aux,annot)) =
  alg.def_val_aux (fold_opt_default_aux alg opt_default_aux, annot)
and fold_pexp_aux alg (Pat_exp (pat,e)) = alg.pat_exp (fold_pat alg.pat_alg pat, fold_exp alg e)
and fold_pexp alg (Pat_aux (pexp_aux,annot)) = alg.pat_aux (fold_pexp_aux alg pexp_aux, annot)
and fold_letbind_aux alg = function
  | LB_val_explicit (t,pat,e) -> alg.lB_val_explicit (t,fold_pat alg.pat_alg pat, fold_exp alg e)
  | LB_val_implicit (pat,e) -> alg.lB_val_implicit (fold_pat alg.pat_alg pat, fold_exp alg e)
and fold_letbind alg (LB_aux (letbind_aux,annot)) = alg.lB_aux (fold_letbind_aux alg letbind_aux, annot)

let id_exp_alg =
  { e_block = (fun es -> E_block es)
  ; e_nondet = (fun es -> E_nondet es)
  ; e_id = (fun id -> E_id id)
  ; e_lit = (fun lit -> (E_lit lit))
  ; e_cast = (fun (typ,e) -> E_cast (typ,e))
  ; e_app = (fun (id,es) -> E_app (id,es))
  ; e_app_infix = (fun (e1,id,e2) -> E_app_infix (e1,id,e2))
  ; e_tuple = (fun es -> E_tuple es)
  ; e_if = (fun (e1,e2,e3) -> E_if (e1,e2,e3))
  ; e_for = (fun (id,e1,e2,e3,order,e4) -> E_for (id,e1,e2,e3,order,e4))
  ; e_vector = (fun es -> E_vector es)
  ; e_vector_indexed = (fun (es,opt2) -> E_vector_indexed (es,opt2))
  ; e_vector_access = (fun (e1,e2) -> E_vector_access (e1,e2))
  ; e_vector_subrange =  (fun (e1,e2,e3) -> E_vector_subrange (e1,e2,e3))
  ; e_vector_update = (fun (e1,e2,e3) -> E_vector_update (e1,e2,e3))
  ; e_vector_update_subrange =  (fun (e1,e2,e3,e4) -> E_vector_update_subrange (e1,e2,e3,e4))
  ; e_vector_append = (fun (e1,e2) -> E_vector_append (e1,e2))
  ; e_list = (fun es -> E_list es)
  ; e_cons = (fun (e1,e2) -> E_cons (e1,e2))
  ; e_record = (fun fexps -> E_record fexps)
  ; e_record_update = (fun (e1,fexp) -> E_record_update (e1,fexp))
  ; e_field = (fun (e1,id) -> (E_field (e1,id)))
  ; e_case = (fun (e1,pexps) -> E_case (e1,pexps))
  ; e_let = (fun (lb,e2) -> E_let (lb,e2))
  ; e_assign = (fun (lexp,e2) -> E_assign (lexp,e2))
  ; e_exit = (fun e1 -> E_exit (e1))
  ; e_return = (fun e1 -> E_return e1)
  ; e_assert = (fun (e1,e2) -> E_assert(e1,e2)) 
  ; e_internal_cast = (fun (a,e1) -> E_internal_cast (a,e1))
  ; e_internal_exp = (fun a -> E_internal_exp a)
  ; e_internal_exp_user = (fun (a1,a2) -> E_internal_exp_user (a1,a2))
  ; e_internal_let = (fun (lexp, e2, e3) -> E_internal_let (lexp,e2,e3))
  ; e_internal_plet = (fun (pat, e1, e2) -> E_internal_plet (pat,e1,e2))
  ; e_internal_return = (fun e -> E_internal_return e)
  ; e_aux = (fun (e,annot) -> E_aux (e,annot))
  ; lEXP_id = (fun id -> LEXP_id id)
  ; lEXP_memory = (fun (id,es) -> LEXP_memory (id,es))
  ; lEXP_cast = (fun (typ,id) -> LEXP_cast (typ,id))
  ; lEXP_tup = (fun tups -> LEXP_tup tups)
  ; lEXP_vector = (fun (lexp,e2) -> LEXP_vector (lexp,e2))
  ; lEXP_vector_range = (fun (lexp,e2,e3) -> LEXP_vector_range (lexp,e2,e3))
  ; lEXP_field = (fun (lexp,id) -> LEXP_field (lexp,id))
  ; lEXP_aux = (fun (lexp,annot) -> LEXP_aux (lexp,annot))
  ; fE_Fexp = (fun (id,e) -> FE_Fexp (id,e))
  ; fE_aux = (fun (fexp,annot) -> FE_aux (fexp,annot))
  ; fES_Fexps = (fun (fexps,b) -> FES_Fexps (fexps,b))
  ; fES_aux = (fun (fexp,annot) -> FES_aux (fexp,annot))
  ; def_val_empty = Def_val_empty
  ; def_val_dec = (fun e -> Def_val_dec e)
  ; def_val_aux = (fun (defval,aux) -> Def_val_aux (defval,aux))
  ; pat_exp = (fun (pat,e) -> (Pat_exp (pat,e)))
  ; pat_aux = (fun (pexp,a) -> (Pat_aux (pexp,a)))
  ; lB_val_explicit = (fun (typ,pat,e) -> LB_val_explicit (typ,pat,e))
  ; lB_val_implicit = (fun (pat,e) -> LB_val_implicit (pat,e))
  ; lB_aux = (fun (lb,annot) -> LB_aux (lb,annot))
  ; pat_alg = id_pat_alg
  }
  

let remove_vector_concat_pat pat =

  (* ivc: bool that indicates whether the exp is in a vector_concat pattern *)
  let remove_typed_patterns =
    fold_pat { id_pat_alg with
               p_aux = (function
                        | (P_typ (_,P_aux (p,_)),annot)
                        | (p,annot) -> 
                           P_aux (p,annot)
                       )
             } in
  
  let pat = remove_typed_patterns pat in

  let fresh_name l =
    let current = fresh_name () in
    Id_aux (Id ("v__" ^ string_of_int current), Parse_ast.Generated l) in
  
  (* expects that P_typ elements have been removed from AST,
     that the length of all vectors involved is known,
     that we don't have indexed vectors *)

  (* introduce names for all patterns of form P_vector_concat *)
  let name_vector_concat_roots =
    { p_lit = (fun lit -> P_lit lit)
    ; p_typ = (fun (typ,p) -> P_typ (typ,p false)) (* cannot happen *)
    ; p_wild = P_wild
    ; p_as = (fun (pat,id) -> P_as (pat true,id))
    ; p_id  = (fun id -> P_id id)
    ; p_app = (fun (id,ps) -> P_app (id, List.map (fun p -> p false) ps))
    ; p_record = (fun (fpats,b) -> P_record (fpats, b))
    ; p_vector = (fun ps -> P_vector (List.map (fun p -> p false) ps))
    ; p_vector_indexed = (fun ps -> P_vector_indexed (List.map (fun (i,p) -> (i,p false)) ps))
    ; p_vector_concat  = (fun ps -> P_vector_concat (List.map (fun p -> p false) ps))
    ; p_tup            = (fun ps -> P_tup (List.map (fun p -> p false) ps))
    ; p_list           = (fun ps -> P_list (List.map (fun p -> p false) ps))
    ; p_aux =
        (fun (pat,((l,_) as annot)) contained_in_p_as ->
          match pat with
          | P_vector_concat pats ->
             (if contained_in_p_as
              then P_aux (pat,annot)
              else P_aux (P_as (P_aux (pat,annot),fresh_name l),annot))
          | _ -> P_aux (pat,annot)
        )
    ; fP_aux = (fun (fpat,annot) -> FP_aux (fpat,annot))
    ; fP_Fpat = (fun (id,p) -> FP_Fpat (id,p false))
    } in

  let pat = (fold_pat name_vector_concat_roots pat) false in

  (* introduce names for all unnamed child nodes of P_vector_concat *)
  let name_vector_concat_elements =
    let p_vector_concat pats =
      let aux ((P_aux (p,((l,_) as a))) as pat) = match p with
        | P_vector _ -> P_aux (P_as (pat,fresh_name l),a)
        | P_id id -> P_aux (P_id id,a)
        | P_as (p,id) -> P_aux (P_as (p,id),a)
        | P_wild -> P_aux (P_wild,a)
        | _ ->
           raise
             (Reporting_basic.err_unreachable
                l "name_vector_concat_elements: Non-vector in vector-concat pattern") in
      P_vector_concat (List.map aux pats) in
    {id_pat_alg with p_vector_concat = p_vector_concat} in

  let pat = fold_pat name_vector_concat_elements pat in

    

  let rec tag_last = function
    | x :: xs -> let is_last = xs = [] in (x,is_last) :: tag_last xs
    | _ -> [] in

  (* remove names from vectors in vector_concat patterns and collect them as declarations for the
     function body or expression *)
  let unname_vector_concat_elements = (* :
        ('a,
         'a pat *      ((tannot exp -> tannot exp) list),
         'a pat_aux *  ((tannot exp -> tannot exp) list),
         'a fpat *     ((tannot exp -> tannot exp) list),
         'a fpat_aux * ((tannot exp -> tannot exp) list))
          pat_alg = *)

    (* build a let-expression of the form "let child = root[i..j] in body" *)
    let letbind_vec (rootid,rannot) (child,cannot) (i,j) =
      let (l,_) = cannot in
      let (Id_aux (Id rootname,_)) = rootid in
      let (Id_aux (Id childname,_)) = child in
      
      let simple_num n : tannot exp =
        let typ = simple_annot (mk_atom_typ (mk_c (big_int_of_int n))) in
        E_aux (E_lit (L_aux (L_num n,l)), (l,typ)) in
      
      let vlength_info (Base ((_,{t = Tapp("vector",[_;TA_nexp nexp;_;_])}),_,_,_,_,_)) =
        nexp in

      let root : tannot exp = E_aux (E_id rootid,rannot) in
      let index_i = simple_num i in
      let index_j : tannot exp = match j with
        | Some j -> simple_num j
        | None ->
           let length_root_nexp = vlength_info (snd rannot) in
           let length_app_exp : tannot exp =
             let typ = mk_atom_typ length_root_nexp in
             let annot = (l,tag_annot typ (External (Some "length"))) in
             E_aux (E_app (Id_aux (Id "length",l),[root]),annot) in
           let minus = Id_aux (Id "-",l) in
           let one_exp : tannot exp = 
             let typ = (mk_atom_typ (mk_c unit_big_int)) in
             let annot = (l,simple_annot typ) in
             E_aux (E_lit (L_aux (L_num 1,l)),annot) in
           
           let typ = mk_atom_typ (mk_sub length_root_nexp (mk_c unit_big_int)) in
           let annot = (l,tag_annot typ (External (Some "minus"))) in
           let exp : tannot exp =
             E_aux (E_app_infix(length_app_exp,minus,one_exp),annot) in
           exp in
      
      let subv = E_aux (E_app (Id_aux (Id "slice_raw",Unknown),
                               [root;index_i;index_j]),cannot) in

      let typ = (Parse_ast.Generated l,simple_annot {t = Tid "unit"}) in
      
      let letbind = LB_val_implicit (P_aux (P_id child,cannot),subv) in
      (LB_aux (letbind,typ),
       (fun body -> E_aux (E_let (LB_aux (letbind,cannot),body),typ)),
       (rootname,childname)) in

    let p_aux = function
      | ((P_as (P_aux (P_vector_concat pats,rannot'),rootid),decls),rannot) ->
         let aux (pos,pat_acc,decl_acc) (P_aux (p,cannot),is_last) = match cannot with
            | (_,Base((_,{t = Tapp ("vector",[_;TA_nexp {nexp = Nconst length};_;_])}),_,_,_,_,_))
            | (_,Base((_,{t = Tabbrev (_,{t = Tapp ("vector",[_;TA_nexp {nexp = Nconst length};_;_])})}),_,_,_,_,_)) ->
               let length  = int_of_big_int length in
               (match p with 
                (* if we see a named vector pattern, remove the name and remember to 
                  declare it later *)
                | P_as (P_aux (p,cannot),cname) ->
                   let (lb,decl,info) = letbind_vec (rootid,rannot) (cname,cannot) (pos,Some(pos+length-1)) in
                   (pos + length, pat_acc @ [P_aux (p,cannot)], decl_acc @ [((lb,decl),info)])
                (* if we see a P_id variable, remember to declare it later *)
                | P_id cname ->
                   let (lb,decl,info) = letbind_vec (rootid,rannot) (cname,cannot) (pos,Some(pos+length-1)) in
                   (pos + length, pat_acc @ [P_aux (P_id cname,cannot)], decl_acc @ [((lb,decl),info)])
                (* normal vector patterns are fine *)
                | _ -> (pos + length, pat_acc @ [P_aux (p,cannot)],decl_acc) )
            (* non-vector patterns aren't *)
            | (l,Base((_,{t = Tapp ("vector",[_;_;_;_])}),_,_,_,_,_))
            | (l,Base((_,{t = Tabbrev (_,{t = Tapp ("vector",[_;_;_;_])})}),_,_,_,_,_)) ->
               if is_last then
                 match p with 
                (* if we see a named vector pattern, remove the name and remember to 
                  declare it later *)
                | P_as (P_aux (p,cannot),cname) ->
                   let (lb,decl,info) = letbind_vec (rootid,rannot) (cname,cannot) (pos,None) in
                   (pos, pat_acc @ [P_aux (p,cannot)], decl_acc @ [((lb,decl),info)])
                (* if we see a P_id variable, remember to declare it later *)
                | P_id cname ->
                   let (lb,decl,info) = letbind_vec (rootid,rannot) (cname,cannot) (pos,None) in
                   (pos, pat_acc @ [P_aux (P_id cname,cannot)], decl_acc @ [((lb,decl),info)])
                (* normal vector patterns are fine *)
                | _ -> (pos, pat_acc @ [P_aux (p,cannot)],decl_acc)
               else
               raise
                 (Reporting_basic.err_unreachable
                    l ("unname_vector_concat_elements: vector of unspecified length in vector-concat pattern"))
            | (l,Base((_,t),_,_,_,_,_)) ->
               raise
                 (Reporting_basic.err_unreachable
                    l ("unname_vector_concat_elements: Non-vector in vector-concat pattern:" ^
                       t_to_string t)
                 )
            | _ -> failwith "has_length: unmatched pattern"
          in
          let pats_tagged = tag_last pats in
          let (_,pats',decls') = List.fold_left aux (0,[],[]) pats_tagged in

          (* abuse P_vector_concat as a P_vector_const pattern: it has the of
          patterns as an argument but they're meant to be consed together *)
          (P_aux (P_as (P_aux (P_vector_concat pats',rannot'),rootid),rannot), decls @ decls')
      | ((p,decls),annot) -> (P_aux (p,annot),decls) in
    
    { p_lit            = (fun lit -> (P_lit lit,[]))
    ; p_wild           = (P_wild,[])
    ; p_as             = (fun ((pat,decls),id) -> (P_as (pat,id),decls))
    ; p_typ            = (fun (typ,(pat,decls)) -> (P_typ (typ,pat),decls))
    ; p_id             = (fun id -> (P_id id,[]))
    ; p_app            = (fun (id,ps) -> let (ps,decls) = List.split ps in
                                         (P_app (id,ps),List.flatten decls))
    ; p_record         = (fun (ps,b) -> let (ps,decls) = List.split ps in
                                        (P_record (ps,b),List.flatten decls))
    ; p_vector         = (fun ps -> let (ps,decls) = List.split ps in
                                    (P_vector ps,List.flatten decls))
    ; p_vector_indexed = (fun ps -> let (is,ps) = List.split ps in
                                    let (ps,decls) = List.split ps in
                                    let ps = List.combine is ps in
                                    (P_vector_indexed ps,List.flatten decls))
    ; p_vector_concat  = (fun ps -> let (ps,decls) = List.split ps in
                                    (P_vector_concat ps,List.flatten decls))
    ; p_tup            = (fun ps -> let (ps,decls) = List.split ps in
                                    (P_tup ps,List.flatten decls))
    ; p_list           = (fun ps -> let (ps,decls) = List.split ps in
                                    (P_list ps,List.flatten decls))
    ; p_aux            = (fun ((pat,decls),annot) -> p_aux ((pat,decls),annot))
    ; fP_aux           = (fun ((fpat,decls),annot) -> (FP_aux (fpat,annot),decls))
    ; fP_Fpat          = (fun (id,(pat,decls)) -> (FP_Fpat (id,pat),decls))
    } in

  let (pat,decls) = fold_pat unname_vector_concat_elements pat in

  let decls =
    let module S = Set.Make(String) in

    let roots_needed =
      List.fold_right
        (fun (_,(rootid,childid)) roots_needed ->
         if S.mem childid roots_needed then
           (* let _ = print_endline rootid in *)
           S.add rootid roots_needed
         else if String.length childid >= 3 && String.sub childid 0 2 = String.sub "v__" 0 2 then
           roots_needed
         else
           S.add rootid roots_needed
        ) decls S.empty in
    List.filter
      (fun (_,(_,childid)) ->  
       S.mem childid roots_needed ||
         String.length childid < 3 ||
           not (String.sub childid 0 2 = String.sub "v__" 0 2))
      decls in

  let (letbinds,decls) =
    let (decls,_) = List.split decls in
    List.split decls in

  let decls = List.fold_left (fun f g x -> f (g x)) (fun b -> b) decls in


  (* at this point shouldn't have P_as patterns in P_vector_concat patterns any more,
     all P_as and P_id vectors should have their declarations in decls.
     Now flatten all vector_concat patterns *)
  
  let flatten =
    let p_vector_concat ps =
      let aux p acc = match p with
        | (P_aux (P_vector_concat pats,_)) -> pats @ acc
        | pat -> pat :: acc in
      P_vector_concat (List.fold_right aux ps []) in
    {id_pat_alg with p_vector_concat = p_vector_concat} in
  
  let pat = fold_pat flatten pat in

  (* at this point pat should be a flat pattern: no vector_concat patterns
     with vector_concats patterns as direct child-nodes anymore *)

  let range a b =
    let rec aux a b = if a > b then [] else a :: aux (a+1) b in
    if a > b then List.rev (aux b a) else aux a b in

  let remove_vector_concats =
    let p_vector_concat ps =
      let aux acc (P_aux (p,annot),is_last) =
        let (l,_) = annot in
        match p,annot with
        | P_vector ps,_ -> acc @ ps
        | P_id _,(_,Base((_,{t = Tapp ("vector", [_;TA_nexp {nexp = Nconst length};_;_])}),_,_,_,_,_))
        | P_id _,(_,Base((_,{t = Tabbrev (_,{t = Tapp ("vector",[_;TA_nexp {nexp = Nconst length};_;_])})}),_,_,_,_,_))
        | P_wild,(_,Base((_,{t = Tapp ("vector", [_;TA_nexp {nexp = Nconst length};_;_])}),_,_,_,_,_))
        | P_wild,(_,Base((_,{t = Tabbrev (_,{t = Tapp ("vector", [_;TA_nexp {nexp = Nconst length};_;_])})}),_,_,_,_,_)) ->
           let wild _ = P_aux (P_wild,(Parse_ast.Generated l,simple_annot {t = Tid "bit"})) in
           acc @ (List.map wild (range 0 ((int_of_big_int length) - 1)))
        | P_id _,(_,Base((_,{t = Tapp ("vector", _)}),_,_,_,_,_))
        | P_id _,(_,Base((_,{t = Tabbrev (_,{t = Tapp ("vector",_)})}),_,_,_,_,_))
        | P_wild,(_,Base((_,{t = Tapp ("vector", _)}),_,_,_,_,_))
        | P_wild,(_,Base((_,{t = Tabbrev (_,{t = Tapp ("vector", _)})}),_,_,_,_,_))
             when is_last ->
           let wild _ = P_aux (P_wild,(Parse_ast.Generated l,simple_annot {t = Tid "bit"})) in
           acc @ [P_aux(P_wild,annot)]
        | P_lit _,(l,_) ->
           raise (Reporting_basic.err_unreachable l "remove_vector_concats: P_lit pattern in vector-concat pattern")
        | _,(l,Base((_,t),_,_,_,_,_)) ->
           raise (Reporting_basic.err_unreachable l ("remove_vector_concats: Non-vector in vector-concat pattern " ^
                       t_to_string t)) in

      let has_length (P_aux (p,annot)) =
        match p,annot with
        | P_vector _,_ -> true
        | P_id _,(_,Base((_,{t = Tapp ("vector", [_;TA_nexp {nexp = Nconst length};_;_])}),_,_,_,_,_))
        | P_id _,(_,Base((_,{t = Tabbrev (_,{t = Tapp ("vector",[_;TA_nexp {nexp = Nconst length};_;_])})}),_,_,_,_,_))
        | P_wild,(_,Base((_,{t = Tapp ("vector", [_;TA_nexp {nexp = Nconst length};_;_])}),_,_,_,_,_))
        | P_wild,(_,Base((_,{t = Tabbrev (_,{t = Tapp ("vector", [_;TA_nexp {nexp = Nconst length};_;_])})}),_,_,_,_,_)) ->
           true
        | P_id _,(_,Base((_,{t = Tapp ("vector", _)}),_,_,_,_,_))
        | P_id _,(_,Base((_,{t = Tabbrev (_,{t = Tapp ("vector",_)})}),_,_,_,_,_))
        | P_wild,(_,Base((_,{t = Tapp ("vector", _)}),_,_,_,_,_))
        | P_wild,(_,Base((_,{t = Tabbrev (_,{t = Tapp ("vector", _)})}),_,_,_,_,_)) ->
           false
        | _ -> failwith "has_length: unmatched pattern"
        in

      let ps_tagged = tag_last ps in
      let ps' = List.fold_left aux [] ps_tagged in
      let last_has_length ps = List.exists (fun (p,b) -> b && has_length p) ps_tagged in

      if last_has_length ps then
        P_vector ps'
      else
        (* If the last vector pattern in the vector_concat pattern has unknown
        length we misuse the P_vector_concat constructor's argument to place in
        the following way: P_vector_concat [x;y; ... ;z] should be mapped to the
        pattern-match x :: y :: .. z, i.e. if x : 'a, then z : vector 'a. *)
        P_vector_concat ps' in

    {id_pat_alg with p_vector_concat = p_vector_concat} in
  
  let pat = fold_pat remove_vector_concats pat in
  
  (pat,letbinds,decls)

(* assumes there are no more E_internal expressions *)
let rewrite_exp_remove_vector_concat_pat rewriters nmap (E_aux (exp,(l,annot)) as full_exp) = 
  let rewrap e = E_aux (e,(l,annot)) in
  let rewrite_rec = rewriters.rewrite_exp rewriters nmap in
  let rewrite_base = rewrite_exp rewriters nmap in
  match exp with
  | E_case (e,ps) ->
     let aux (Pat_aux (Pat_exp (pat,body),annot')) =
       let (pat,_,decls) = remove_vector_concat_pat pat in
       Pat_aux (Pat_exp (pat,decls (rewrite_rec body)),annot') in
     rewrap (E_case (rewrite_rec e,List.map aux ps))
  | E_let (LB_aux (LB_val_explicit (typ,pat,v),annot'),body) ->
     let (pat,_,decls) = remove_vector_concat_pat pat in
     rewrap (E_let (LB_aux (LB_val_explicit (typ,pat,rewrite_rec v),annot'),
                    decls (rewrite_rec body)))
  | E_let (LB_aux (LB_val_implicit (pat,v),annot'),body) ->
     let (pat,_,decls) = remove_vector_concat_pat pat in
     rewrap (E_let (LB_aux (LB_val_implicit (pat,rewrite_rec v),annot'),
                    decls (rewrite_rec body)))
  | exp -> rewrite_base full_exp

let rewrite_fun_remove_vector_concat_pat
      rewriters (FD_aux (FD_function(recopt,tannotopt,effectopt,funcls),(l,fdannot))) = 
  let rewrite_funcl (FCL_aux (FCL_Funcl(id,pat,exp),(l,annot))) =
    let (pat,_,decls) = remove_vector_concat_pat pat in
    (FCL_aux (FCL_Funcl (id,pat,rewriters.rewrite_exp rewriters None (decls exp)),(l,annot))) 
  in FD_aux (FD_function(recopt,tannotopt,effectopt,List.map rewrite_funcl funcls),(l,fdannot))

let rewrite_defs_remove_vector_concat_pat rewriters (Defs defs) =
  let rewrite_def d =
    let d = rewriters.rewrite_def rewriters d in
    match d with
    | DEF_val (LB_aux (LB_val_explicit (t,pat,exp),a)) ->
       let (pat,letbinds,_) = remove_vector_concat_pat pat in
       let defvals = List.map (fun lb -> DEF_val lb) letbinds in
       [DEF_val (LB_aux (LB_val_explicit (t,pat,exp),a))] @ defvals
    | DEF_val (LB_aux (LB_val_implicit (pat,exp),a)) -> 
       let (pat,letbinds,_) = remove_vector_concat_pat pat in
       let defvals = List.map (fun lb -> DEF_val lb) letbinds in
       [DEF_val (LB_aux (LB_val_implicit (pat,exp),a))] @ defvals
    | d -> [rewriters.rewrite_def rewriters d] in
  Defs (List.flatten (List.map rewrite_def defs))

let rewrite_defs_remove_vector_concat defs = rewrite_defs_base
    {rewrite_exp = rewrite_exp_remove_vector_concat_pat;
     rewrite_pat = rewrite_pat;
     rewrite_let = rewrite_let;
     rewrite_lexp = rewrite_lexp;
     rewrite_fun = rewrite_fun_remove_vector_concat_pat;
     rewrite_def = rewrite_def;
     rewrite_defs = rewrite_defs_remove_vector_concat_pat} defs
    
(*Expects to be called after rewrite_defs; thus the following should not appear:
  internal_exp of any form
  lit vectors in patterns or expressions
 *)
let rewrite_exp_lift_assign_intro rewriters nmap ((E_aux (exp,(l,annot))) as full_exp) = 
  let rewrap e = E_aux (e,(l,annot)) in
  let rewrap_effects e effsum =
    let (Base (t,tag,nexps,eff,_,bounds)) = annot in
    E_aux (e,(l,Base (t,tag,nexps,eff,effsum,bounds))) in
  let rewrite_rec = rewriters.rewrite_exp rewriters nmap in
  let rewrite_base = rewrite_exp rewriters nmap in
  match exp with
  | E_block exps ->
    let rec walker exps = match exps with
      | [] -> []
      | (E_aux(E_assign(le,e), (l, Base((_,t),Emp_intro,_,_,_,_))))::exps ->
        let le' = rewriters.rewrite_lexp rewriters nmap le in
        let e' = rewrite_base e in
        let exps' = walker exps in
        let effects = eff_union_exps exps' in
        [E_aux (E_internal_let(le', e', E_aux(E_block exps', (l, simple_annot_efr {t=Tid "unit"} effects))),
                 (l, simple_annot_efr t (eff_union_exps (e::exps'))))]
      | ((E_aux(E_if(c,t,e),(l,annot))) as exp)::exps ->
        let vars_t = introduced_variables t in
        let vars_e = introduced_variables e in
        let new_vars = Envmap.intersect vars_t vars_e in
        if Envmap.is_empty new_vars
         then (rewrite_base exp)::walker exps
         else
           let new_nmap = match nmap with
             | None -> Some(Nexpmap.empty,new_vars)
             | Some(nm,s) -> Some(nm, Envmap.union new_vars s) in
           let c' = rewrite_base c in
           let t' = rewriters.rewrite_exp rewriters new_nmap t in
           let e' = rewriters.rewrite_exp rewriters new_nmap e in
           let exps' = walker exps in
           fst ((Envmap.fold 
                  (fun (res,effects) i (t,e) ->
                let bitlit =  E_aux (E_lit (L_aux(L_zero, Parse_ast.Generated l)),
                                     (Parse_ast.Generated l, simple_annot bit_t)) in
                let rangelit = E_aux (E_lit (L_aux (L_num 0, Parse_ast.Generated l)),
                                      (Parse_ast.Generated l, simple_annot nat_t)) in
                let set_exp =
                  match t.t with
                  | Tid "bit" | Tabbrev(_,{t=Tid "bit"}) -> bitlit
                  | Tapp("range", _) | Tapp("atom", _) -> rangelit
                  | Tapp("vector", [_;_;_;TA_typ ( {t=Tid "bit"} | {t=Tabbrev(_,{t=Tid "bit"})})])
                  | Tapp(("reg"|"register"),[TA_typ ({t = Tapp("vector",
                                                               [_;_;_;TA_typ ( {t=Tid "bit"}
                                                                             | {t=Tabbrev(_,{t=Tid "bit"})})])})])
                  | Tabbrev(_,{t = Tapp("vector",
                                        [_;_;_;TA_typ ( {t=Tid "bit"}
                                                      | {t=Tabbrev(_,{t=Tid "bit"})})])}) ->
                    E_aux (E_vector_indexed([], Def_val_aux(Def_val_dec bitlit,
                                                            (Parse_ast.Generated l,simple_annot bit_t))),
                           (Parse_ast.Generated l, simple_annot t))
                  | _ -> e in
                let unioneffs = union_effects effects (get_effsum_exp set_exp) in
                ([E_aux (E_internal_let (LEXP_aux (LEXP_id (Id_aux (Id i, Parse_ast.Generated l)),
                                                  (Parse_ast.Generated l, (tag_annot t Emp_intro))),
                                        set_exp,
                                        E_aux (E_block res, (Parse_ast.Generated l, (simple_annot_efr unit_t effects)))),
                        (Parse_ast.Generated l, simple_annot_efr unit_t unioneffs))],unioneffs)))
             (E_aux(E_if(c',t',e'),(Parse_ast.Generated l, annot))::exps',eff_union_exps (c'::t'::e'::exps')) new_vars)
      | e::exps -> (rewrite_rec e)::(walker exps)
    in
    rewrap (E_block (walker exps))
  | E_assign(le,e) ->
    (match annot with
     | Base((_,t),Emp_intro,_,_,_,_) ->
       let le' = rewriters.rewrite_lexp rewriters nmap le in
       let e' = rewrite_base e in
       let effects = get_effsum_exp e' in
       (match le' with
        | LEXP_aux(_, (_,Base(_,Emp_intro,_,_,_,_))) ->
          rewrap_effects
            (E_internal_let(le', e', E_aux(E_block [], (l, simple_annot_efr unit_t effects))))
            effects
        | LEXP_aux(_, (_,Base(_,_,_,_,efr,_))) ->
          let effects' = union_effects effects efr in
          E_aux((E_assign(le', e')),(l, tag_annot_efr unit_t Emp_set effects'))
        | _ -> assert false)
     | _ -> rewrite_base full_exp)
  | _ -> rewrite_base full_exp

let rewrite_lexp_lift_assign_intro rewriters map ((LEXP_aux(lexp,(l,annot))) as le) = 
  let rewrap le = LEXP_aux(le,(l,annot)) in
  let rewrite_base = rewrite_lexp rewriters map in
  match lexp with
  | LEXP_id (Id_aux (Id i, _)) | LEXP_cast (_,(Id_aux (Id i,_))) ->
    (match annot with
    | Base((p,t),Emp_intro,cs,e1,e2,bs) ->
      (match map with
       | Some(_,s) ->
         (match Envmap.apply s i with
          | None -> rewrap lexp
          | Some _ ->
            let ls = BE_aux(BE_lset,l) in
            LEXP_aux(lexp,(l,(Base((p,t),Emp_set,cs,add_effect ls e1, add_effect ls e2,bs)))))
       | _ -> rewrap lexp)
    | _ -> rewrap lexp)
  | _ -> rewrite_base le


let rewrite_defs_exp_lift_assign defs = rewrite_defs_base
    {rewrite_exp = rewrite_exp_lift_assign_intro;
     rewrite_pat = rewrite_pat;
     rewrite_let = rewrite_let;
     rewrite_lexp = rewrite_lexp_lift_assign_intro;
     rewrite_fun = rewrite_fun;
     rewrite_def = rewrite_def;
     rewrite_defs = rewrite_defs_base} defs
    
let rewrite_exp_separate_ints rewriters nmap ((E_aux (exp,(l,annot))) as full_exp) =
  let tparms,t,tag,nexps,eff,cum_eff,bounds = match annot with
    | Base((tparms,t),tag,nexps,eff,cum_eff,bounds) -> tparms,t,tag,nexps,eff,cum_eff,bounds
    | _ -> [],unit_t,Emp_local,[],pure_e,pure_e,nob in
  let rewrap e = E_aux (e,(l,annot)) in
  let rewrap_effects e effsum =
    E_aux (e,(l,Base ((tparms,t),tag,nexps,eff,effsum,bounds))) in
  let rewrite_rec = rewriters.rewrite_exp rewriters nmap in
  let rewrite_base = rewrite_exp rewriters nmap in
  match exp with
  | E_lit (L_aux (((L_num _) as lit),_)) ->
    (match (is_within_machine64 t nexps) with
     | Yes -> let _ = Printf.eprintf "Rewriter of num_const, within 64bit int yes\n" in rewrite_base full_exp
     | Maybe -> let _ = Printf.eprintf "Rewriter of num_const, within 64bit int maybe\n" in rewrite_base full_exp
     | No -> let _ = Printf.eprintf "Rewriter of num_const, within 64bit int no\n" in E_aux(E_app(Id_aux (Id "integer_of_int",l),[rewrite_base full_exp]),
                   (l, Base((tparms,t),External(None),nexps,eff,cum_eff,bounds))))
  | E_cast (typ, exp) -> rewrap (E_cast (typ, rewrite_rec exp))
  | E_app (id,exps) -> rewrap (E_app (id,List.map rewrite_rec exps))
  | E_app_infix(el,id,er) -> rewrap (E_app_infix(rewrite_rec el,id,rewrite_rec er))
  | E_for (id, e1, e2, e3, o, body) ->
      rewrap (E_for (id, rewrite_rec e1, rewrite_rec e2, rewrite_rec e3, o, rewrite_rec body))
  | E_vector_access (vec,index) -> rewrap (E_vector_access (rewrite_rec vec,rewrite_rec index))
  | E_vector_subrange (vec,i1,i2) ->
    rewrap (E_vector_subrange (rewrite_rec vec,rewrite_rec i1,rewrite_rec i2))
  | E_vector_update (vec,index,new_v) -> 
    rewrap (E_vector_update (rewrite_rec vec,rewrite_rec index,rewrite_rec new_v))
  | E_vector_update_subrange (vec,i1,i2,new_v) ->
    rewrap (E_vector_update_subrange (rewrite_rec vec,rewrite_rec i1,rewrite_rec i2,rewrite_rec new_v))
  | E_case (exp ,pexps) -> 
    rewrap (E_case (rewrite_rec exp,
                    (List.map 
                       (fun (Pat_aux (Pat_exp(p,e),pannot)) -> 
                          Pat_aux (Pat_exp(rewriters.rewrite_pat rewriters nmap p,rewrite_rec e),pannot)) pexps)))
  | E_let (letbind,body) -> rewrap (E_let(rewriters.rewrite_let rewriters nmap letbind,rewrite_rec body))
  | E_internal_let (lexp,exp,body) ->
    rewrap (E_internal_let (rewriters.rewrite_lexp rewriters nmap lexp, rewrite_rec exp, rewrite_rec body))
  | _ -> rewrite_base full_exp

let rewrite_defs_separate_numbs defs = rewrite_defs_base
    {rewrite_exp = rewrite_exp_separate_ints;
     rewrite_pat = rewrite_pat;
     rewrite_let = rewrite_let; (*will likely need a new one?*)
     rewrite_lexp = rewrite_lexp; (*will likely need a new one?*)
     rewrite_fun = rewrite_fun;
     rewrite_def = rewrite_def;
     rewrite_defs = rewrite_defs_base} defs

let rewrite_defs_ocaml defs =
  let defs_sorted = top_sort_defs defs in
  let defs_vec_concat_removed = rewrite_defs_remove_vector_concat defs_sorted in
  let defs_lifted_assign = rewrite_defs_exp_lift_assign defs_vec_concat_removed in
(*  let defs_separate_nums = rewrite_defs_separate_numbs defs_lifted_assign in *)
  defs_lifted_assign

let rewrite_defs_remove_blocks =
  let letbind_wild v body =
    let (E_aux (_,(l,_))) = v in
    let annot_pat = (Parse_ast.Generated l,simple_annot (get_type v)) in
    let annot_lb = (Parse_ast.Generated l,simple_annot_efr (get_type v) (get_effsum_exp v)) in
    let annot_let = (Parse_ast.Generated l,simple_annot_efr (get_type body) (eff_union_exps [v;body])) in
    E_aux (E_let (LB_aux (LB_val_implicit (P_aux (P_wild,annot_pat),v),annot_lb),body),annot_let) in

  let rec f l = function
    | [] -> E_aux (E_lit (L_aux (L_unit,Parse_ast.Generated l)), (Parse_ast.Generated l,simple_annot ({t = Tid "unit"})))
    | [e] -> e  (* check with Kathy if that annotation is fine *)
    | e :: es -> letbind_wild e (f l es) in

  let e_aux = function
    | (E_block es,(l,_)) -> f l es
    | (e,annot) -> E_aux (e,annot) in
    
  let alg = { id_exp_alg with e_aux = e_aux } in

  rewrite_defs_base
    {rewrite_exp = (fun _ _ -> fold_exp alg)
    ; rewrite_pat = rewrite_pat
    ; rewrite_let = rewrite_let
    ; rewrite_lexp = rewrite_lexp
    ; rewrite_fun = rewrite_fun
    ; rewrite_def = rewrite_def
    ; rewrite_defs = rewrite_defs_base
    }



let fresh_id ((l,_) as annot) =
  let current = fresh_name () in
  let id = Id_aux (Id ("w__" ^ string_of_int current), Parse_ast.Generated l) in
  let annot_var = (Parse_ast.Generated l,simple_annot (get_type_annot annot)) in
  E_aux (E_id id, annot_var)
        
let letbind (v : 'a exp) (body : 'a exp -> 'a exp) : 'a exp =
  (* body is a function : E_id variable -> actual body *)
  match get_type v with
  | {t = Tid "unit"} ->
     let (E_aux (_,(l,annot))) = v in
     let e = E_aux (E_lit (L_aux (L_unit,Parse_ast.Generated l)),(Parse_ast.Generated l,simple_annot unit_t))  in
     let body = body e in
     let annot_pat = (Parse_ast.Generated l,simple_annot unit_t) in
     let annot_lb = annot_pat in
     let annot_let = (Parse_ast.Generated l,simple_annot_efr (get_type body) (eff_union_exps [v;body])) in
     let pat = P_aux (P_wild,annot_pat) in
     
     E_aux (E_let (LB_aux (LB_val_implicit (pat,v),annot_lb),body),annot_let)
  | _ -> 
     let (E_aux (_,((l,_) as annot))) = v in
     let ((E_aux (E_id id,_)) as e_id) = fresh_id annot in
     let body = body e_id in
     
     let annot_pat = (Parse_ast.Generated l,simple_annot (get_type v)) in
     let annot_lb = annot_pat in
     let annot_let = (Parse_ast.Generated l,simple_annot_efr (get_type body) (eff_union_exps [v;body])) in
     let pat = P_aux (P_id id,annot_pat) in
     
     E_aux (E_let (LB_aux (LB_val_implicit (pat,v),annot_lb),body),annot_let)


let rec mapCont (f : 'b -> ('b -> 'a exp) -> 'a exp) (l : 'b list) (k : 'b list -> 'a exp) : 'a exp = 
  match l with
  | [] -> k []
  | exp :: exps -> f exp (fun exp -> mapCont f exps (fun exps -> k (exp :: exps)))
                
let rewrite_defs_letbind_effects  =  

  let rec value ((E_aux (exp_aux,_)) as exp) =
    not (effectful exp) && not (updates_vars exp)
  and value_optdefault (Def_val_aux (o,_)) = match o with
    | Def_val_empty -> true
    | Def_val_dec e -> value e
  and value_fexps (FES_aux (FES_Fexps (fexps,_),_)) =
    List.fold_left (fun b (FE_aux (FE_Fexp (_,e),_)) -> b && value e) true fexps in


  let rec n_exp_name (exp : 'a exp) (k : 'a exp -> 'a exp) : 'a exp =
    n_exp exp (fun exp -> if value exp then k exp else letbind exp k)

  and n_exp_pure (exp : 'a exp) (k : 'a exp -> 'a exp) : 'a exp =
    n_exp exp (fun exp -> if not (effectful exp || updates_vars exp) then k exp else letbind exp k)

  and n_exp_nameL (exps : 'a exp list) (k : 'a exp list -> 'a exp) : 'a exp =
    mapCont n_exp_name exps k

  and n_fexp (fexp : 'a fexp) (k : 'a fexp -> 'a exp) : 'a exp =
    let (FE_aux (FE_Fexp (id,exp),annot)) = fexp in
    n_exp_name exp (fun exp -> 
    k (fix_effsum_fexp (FE_aux (FE_Fexp (id,exp),annot))))

  and n_fexpL (fexps : 'a fexp list) (k : 'a fexp list -> 'a exp) : 'a exp =
    mapCont n_fexp fexps k

  and n_pexp (newreturn : bool) (pexp : 'a pexp) (k : 'a pexp -> 'a exp) : 'a exp =
    let (Pat_aux (Pat_exp (pat,exp),annot)) = pexp in
    k (fix_effsum_pexp (Pat_aux (Pat_exp (pat,n_exp_term newreturn exp), annot)))

  and n_pexpL (newreturn : bool) (pexps : 'a pexp list) (k : 'a pexp list -> 'a exp) : 'a exp =
    mapCont (n_pexp newreturn) pexps k

  and n_fexps (fexps : 'a fexps) (k : 'a fexps -> 'a exp) : 'a exp = 
    let (FES_aux (FES_Fexps (fexps_aux,b),annot)) = fexps in
    n_fexpL fexps_aux (fun fexps_aux -> 
    k (fix_effsum_fexps (FES_aux (FES_Fexps (fexps_aux,b),annot))))

  and n_opt_default (opt_default : 'a opt_default) (k : 'a opt_default -> 'a exp) : 'a exp = 
    let (Def_val_aux (opt_default,annot)) = opt_default in
    match opt_default with
    | Def_val_empty -> k (Def_val_aux (Def_val_empty,annot))
    | Def_val_dec exp ->
       n_exp_name exp (fun exp -> 
       k (fix_effsum_opt_default (Def_val_aux (Def_val_dec exp,annot))))

  and n_lb (lb : 'a letbind) (k : 'a letbind -> 'a exp) : 'a exp =
    let (LB_aux (lb,annot)) = lb in
    match lb with
    | LB_val_explicit (typ,pat,exp1) ->
       n_exp exp1 (fun exp1 -> 
       k (fix_effsum_lb (LB_aux (LB_val_explicit (typ,pat,exp1),annot))))
    | LB_val_implicit (pat,exp1) ->
       n_exp exp1 (fun exp1 -> 
       k (fix_effsum_lb (LB_aux (LB_val_implicit (pat,exp1),annot))))

  and n_lexp (lexp : 'a lexp) (k : 'a lexp -> 'a exp) : 'a exp =
    let (LEXP_aux (lexp_aux,annot)) = lexp in
    match lexp_aux with
    | LEXP_id _ -> k lexp
    | LEXP_memory (id,es) ->
       n_exp_nameL es (fun es -> 
       k (fix_effsum_lexp (LEXP_aux (LEXP_memory (id,es),annot))))
    | LEXP_cast (typ,id) -> 
       k (fix_effsum_lexp (LEXP_aux (LEXP_cast (typ,id),annot)))
    | LEXP_vector (lexp,e) ->
       n_lexp lexp (fun lexp -> 
       n_exp_name e (fun e -> 
       k (fix_effsum_lexp (LEXP_aux (LEXP_vector (lexp,e),annot)))))
    | LEXP_vector_range (lexp,e1,e2) ->
       n_lexp lexp (fun lexp ->
       n_exp_name e1 (fun e1 ->
       n_exp_name e2 (fun e2 ->
       k (fix_effsum_lexp (LEXP_aux (LEXP_vector_range (lexp,e1,e2),annot))))))
    | LEXP_field (lexp,id) ->
       n_lexp lexp (fun lexp ->
       k (fix_effsum_lexp (LEXP_aux (LEXP_field (lexp,id),annot))))
    | _ -> failwith "n_lexp: unhandled lexp"

  and n_exp_term (newreturn : bool) (exp : 'a exp) : 'a exp =
    let (E_aux (_,(l,_))) = exp in
    let exp =
      if newreturn then
        E_aux (E_internal_return exp,(Parse_ast.Generated l,simple_annot_efr (get_type exp) (get_effsum_exp exp)))
      else
        exp in
    (* n_exp_term forces an expression to be translated into a form 
       "let .. let .. let .. in EXP" where EXP has no effect and does not update
       variables *)
    n_exp_pure exp (fun exp -> exp)

  and n_exp (E_aux (exp_aux,annot) as exp : 'a exp) (k : 'a exp -> 'a exp) : 'a exp = 

    let rewrap e = fix_effsum_exp (E_aux (e,annot)) in

    match exp_aux with
    | E_block es -> failwith "E_block should have been removed till now"
    | E_nondet _ -> failwith "E_nondet not supported"
    | E_id id -> k exp
    | E_lit _ -> k exp
    | E_cast (typ,exp') ->
       n_exp_name exp' (fun exp' ->
       k (rewrap (E_cast (typ,exp'))))
    | E_app (id,exps) ->
       n_exp_nameL exps (fun exps ->
       k (rewrap (E_app (id,exps))))
    | E_app_infix (exp1,id,exp2) ->
       n_exp_name exp1 (fun exp1 ->
       n_exp_name exp2 (fun exp2 ->
       k (rewrap (E_app_infix (exp1,id,exp2)))))
    | E_tuple exps ->
       n_exp_nameL exps (fun exps ->
       k (rewrap (E_tuple exps)))
    | E_if (exp1,exp2,exp3) ->
       n_exp_name exp1 (fun exp1 ->
       let (E_aux (_,annot2)) = exp2 in
       let (E_aux (_,annot3)) = exp3 in
       let newreturn = effectful exp2 || effectful exp3 in
       let exp2 = n_exp_term newreturn exp2 in
       let exp3 = n_exp_term newreturn exp3 in
       k (rewrap (E_if (exp1,exp2,exp3))))
    | E_for (id,start,stop,by,dir,body) ->
       n_exp_name start (fun start -> 
       n_exp_name stop (fun stop ->
       n_exp_name by (fun by ->
       let body = n_exp_term (effectful body) body in
       k (rewrap (E_for (id,start,stop,by,dir,body))))))
    | E_vector exps ->
       n_exp_nameL exps (fun exps ->
       k (rewrap (E_vector exps)))
    | E_vector_indexed (exps,opt_default)  ->
       let (is,exps) = List.split exps in
       n_exp_nameL exps (fun exps -> 
       n_opt_default opt_default (fun opt_default ->
       let exps = List.combine is exps in
       k (rewrap (E_vector_indexed (exps,opt_default)))))
    | E_vector_access (exp1,exp2) ->
       n_exp_name exp1 (fun exp1 ->
       n_exp_name exp2 (fun exp2 ->
       k (rewrap (E_vector_access (exp1,exp2)))))
    | E_vector_subrange (exp1,exp2,exp3) ->
       n_exp_name exp1 (fun exp1 -> 
       n_exp_name exp2 (fun exp2 -> 
       n_exp_name exp3 (fun exp3 ->
       k (rewrap (E_vector_subrange (exp1,exp2,exp3))))))
    | E_vector_update (exp1,exp2,exp3) ->
       n_exp_name exp1 (fun exp1 -> 
       n_exp_name exp2 (fun exp2 -> 
       n_exp_name exp3 (fun exp3 ->
       k (rewrap (E_vector_update (exp1,exp2,exp3))))))
    | E_vector_update_subrange (exp1,exp2,exp3,exp4) ->
       n_exp_name exp1 (fun exp1 -> 
       n_exp_name exp2 (fun exp2 -> 
       n_exp_name exp3 (fun exp3 -> 
       n_exp_name exp4 (fun exp4 ->
       k (rewrap (E_vector_update_subrange (exp1,exp2,exp3,exp4)))))))
    | E_vector_append (exp1,exp2) ->
       n_exp_name exp1 (fun exp1 ->
       n_exp_name exp2 (fun exp2 ->
       k (rewrap (E_vector_append (exp1,exp2)))))
    | E_list exps ->
       n_exp_nameL exps (fun exps ->
       k (rewrap (E_list exps)))
    | E_cons (exp1,exp2) -> 
       n_exp_name exp1 (fun exp1 ->
       n_exp_name exp2 (fun exp2 ->
       k (rewrap (E_cons (exp1,exp2)))))
    | E_record fexps ->
       n_fexps fexps (fun fexps ->
       k (rewrap (E_record fexps)))
    | E_record_update (exp1,fexps) -> 
       n_exp_name exp1 (fun exp1 ->
       n_fexps fexps (fun fexps ->
       k (rewrap (E_record_update (exp1,fexps)))))
    | E_field (exp1,id) ->
       n_exp_name exp1 (fun exp1 ->
       k (rewrap (E_field (exp1,id))))
    | E_case (exp1,pexps) ->
       let newreturn =
         List.fold_left
           (fun b (Pat_aux (_,(_,Base (_,_,_,_,effs,_)))) -> b || effectful_effs effs)
           false pexps in
       n_exp_name exp1 (fun exp1 -> 
       n_pexpL newreturn pexps (fun pexps ->
       k (rewrap (E_case (exp1,pexps)))))
    | E_let (lb,body) ->
       n_lb lb (fun lb -> 
       rewrap (E_let (lb,n_exp body k)))
    | E_sizeof nexp ->
       k (rewrap (E_sizeof nexp))
    | E_sizeof_internal annot ->
       k (rewrap (E_sizeof_internal annot))
    | E_assign (lexp,exp1) ->
       n_lexp lexp (fun lexp ->
       n_exp_name exp1 (fun exp1 ->
       k (rewrap (E_assign (lexp,exp1)))))
    | E_exit exp' -> k (E_aux (E_exit (n_exp_term (effectful exp') exp'),annot))
    | E_assert (exp1,exp2) ->
       n_exp exp1 (fun exp1 ->
       n_exp exp2 (fun exp2 ->
       k (rewrap (E_assert (exp1,exp2)))))
    | E_internal_cast (annot',exp') ->
       n_exp_name exp' (fun exp' ->
       k (rewrap (E_internal_cast (annot',exp'))))
    | E_internal_exp _ -> k exp
    | E_internal_exp_user _ -> k exp
    | E_internal_let (lexp,exp1,exp2) ->
       n_lexp lexp (fun lexp ->
       n_exp exp1 (fun exp1 ->
       rewrap (E_internal_let (lexp,exp1,n_exp exp2 k))))
    | E_internal_return exp1 ->
       n_exp_name exp1 (fun exp1 ->
       k (rewrap (E_internal_return exp1)))
    | E_comment str ->
      k (rewrap (E_comment str))
    | E_comment_struc exp' ->
       n_exp exp' (fun exp' ->
               k (rewrap (E_comment_struc exp')))
    | E_return exp' ->
       n_exp_name exp' (fun exp' ->
       k (rewrap (E_return exp')))
    | E_internal_plet _ -> failwith "E_internal_plet should not be here yet" in

  let rewrite_fun _ (FD_aux (FD_function(recopt,tannotopt,effectopt,funcls),fdannot)) = 
    let newreturn =
      List.fold_left
        (fun b (FCL_aux (FCL_Funcl(id,pat,exp),annot)) ->
         b || effectful_effs (get_localeff_annot annot)) false funcls in
    let rewrite_funcl (FCL_aux (FCL_Funcl(id,pat,exp),annot)) =
      let _ = reset_fresh_name_counter () in
      FCL_aux (FCL_Funcl (id,pat,n_exp_term newreturn exp),annot)
    in FD_aux (FD_function(recopt,tannotopt,effectopt,List.map rewrite_funcl funcls),fdannot) in
  rewrite_defs_base
    {rewrite_exp = rewrite_exp
    ; rewrite_pat = rewrite_pat
    ; rewrite_let = rewrite_let
    ; rewrite_lexp = rewrite_lexp
    ; rewrite_fun = rewrite_fun
    ; rewrite_def = rewrite_def
    ; rewrite_defs = rewrite_defs_base
    }

let rewrite_defs_effectful_let_expressions =

  let e_let (lb,body) = 
    match lb with
    | LB_aux (LB_val_explicit (_,pat,exp'),annot')
    | LB_aux (LB_val_implicit (pat,exp'),annot') ->
       if effectful exp'
       then E_internal_plet (pat,exp',body)
       else E_let (lb,body) in
                             
  let e_internal_let = fun (lexp,exp1,exp2) ->
    if effectful exp1 then
      match lexp with
      | LEXP_aux (LEXP_id id,annot)
      | LEXP_aux (LEXP_cast (_,id),annot) ->
         E_internal_plet (P_aux (P_id id,annot),exp1,exp2)
      | _ -> failwith "E_internal_plet with unexpected lexp"
    else E_internal_let (lexp,exp1,exp2) in

  let alg = { id_exp_alg with e_let = e_let; e_internal_let = e_internal_let } in
  rewrite_defs_base
    {rewrite_exp = (fun _ _ -> fold_exp alg)
    ; rewrite_pat = rewrite_pat
    ; rewrite_let = rewrite_let
    ; rewrite_lexp = rewrite_lexp
    ; rewrite_fun = rewrite_fun
    ; rewrite_def = rewrite_def
    ; rewrite_defs = rewrite_defs_base
    }

             
(* Now all expressions have no blocks anymore, any term is a sequence of let-expressions,
 * internal let-expressions, or internal plet-expressions ended by a term that does not
 * access memory or registers and does not update variables *)

let dedup eq =
  List.fold_left (fun acc e -> if List.exists (eq e) acc then acc else e :: acc) []

let eqidtyp (id1,_) (id2,_) =
  let name1 = match id1 with Id_aux ((Id name | DeIid name),_) -> name in
  let name2 = match id2 with Id_aux ((Id name | DeIid name),_) -> name in
  name1 = name2

let find_updated_vars exp = 
  let ( @@ ) (a,b) (a',b') = (a @ a',b @ b') in
  let lapp2 (l : (('a list * 'b list) list)) : ('a list * 'b list) =
    List.fold_left
      (fun ((intros_acc : 'a list),(updates_acc : 'b list)) (intros,updates) ->
       (intros_acc @ intros, updates_acc @ updates)) ([],[]) l in
  
  let (intros,updates) =
    fold_exp
      { e_aux = (fun (e,_) -> e)
      ; e_id = (fun _ -> ([],[]))
      ; e_lit = (fun _ -> ([],[]))
      ; e_cast = (fun (_,e) -> e)
      ; e_block = (fun es -> lapp2 es)
      ; e_nondet = (fun es -> lapp2 es)
      ; e_app = (fun (_,es) -> lapp2 es)
      ; e_app_infix = (fun (e1,_,e2) -> e1 @@ e2)
      ; e_tuple = (fun es -> lapp2 es)
      ; e_if = (fun (e1,e2,e3) -> e1 @@ e2 @@ e3)
      ; e_for = (fun (_,e1,e2,e3,_,e4) -> e1 @@ e2 @@ e3 @@ e4)
      ; e_vector = (fun es -> lapp2 es)
      ; e_vector_indexed = (fun (es,opt) -> opt @@ lapp2 (List.map snd es))
      ; e_vector_access = (fun (e1,e2) -> e1 @@ e2)
      ; e_vector_subrange =  (fun (e1,e2,e3) -> e1 @@ e2 @@ e3)
      ; e_vector_update = (fun (e1,e2,e3) -> e1 @@ e2 @@ e3)
      ; e_vector_update_subrange =  (fun (e1,e2,e3,e4) -> e1 @@ e2 @@ e3 @@ e4)
      ; e_vector_append = (fun (e1,e2) -> e1 @@ e2)
      ; e_list = (fun es -> lapp2 es)
      ; e_cons = (fun (e1,e2) -> e1 @@ e2)
      ; e_record = (fun fexps -> fexps)
      ; e_record_update = (fun (e1,fexp) -> e1 @@ fexp)
      ; e_field = (fun (e1,id) -> e1)
      ; e_case = (fun (e1,pexps) -> e1 @@ lapp2 pexps)
      ; e_let = (fun (lb,e2) -> lb @@ e2)
      ; e_assign = (fun ((ids,acc),e2) -> ([],ids) @@ acc @@ e2)
      ; e_exit = (fun e1 -> ([],[]))
      ; e_return = (fun e1 -> e1)
      ; e_assert = (fun (e1,e2) -> ([],[]))
      ; e_internal_cast = (fun (_,e1) -> e1)
      ; e_internal_exp = (fun _ -> ([],[]))
      ; e_internal_exp_user = (fun _ -> ([],[]))
      ; e_internal_let =
          (fun (([id],acc),e2,e3) ->
           let (xs,ys) = ([id],[]) @@ acc @@ e2 @@ e3 in
           let ys = List.filter (fun id2 -> not (eqidtyp id id2)) ys in
           (xs,ys))
      ; e_internal_plet = (fun (_, e1, e2) -> e1 @@ e2)
      ; e_internal_return = (fun e -> e)
      ; lEXP_id = (fun id -> (Some id,[],([],[])))
      ; lEXP_memory = (fun (_,es) -> (None,[],lapp2 es))
      ; lEXP_cast = (fun (_,id) -> (Some id,[],([],[])))
      ; lEXP_tup = (fun tups -> failwith "FORCHRISTOPHER:: this needs implementing, not sure what you want to do")
      ; lEXP_vector = (fun ((ids,acc),e1) -> (None,ids,acc @@ e1))
      ; lEXP_vector_range = (fun ((ids,acc),e1,e2) -> (None,ids,acc @@ e1 @@ e2))
      ; lEXP_field = (fun ((ids,acc),_) -> (None,ids,acc))
      ; lEXP_aux =
          (function
            | ((Some id,ids,acc),((_,Base (_,(Emp_set | Emp_intro),_,_,_,_)) as annot)) ->
               ((id,annot) :: ids,acc)
            | ((_,ids,acc),_) -> (ids,acc)
          )
      ; fE_Fexp = (fun (_,e) -> e)
      ; fE_aux = (fun (fexp,_) -> fexp)
      ; fES_Fexps = (fun (fexps,_) -> lapp2 fexps)
      ; fES_aux = (fun (fexp,_) -> fexp)
      ; def_val_empty = ([],[])
      ; def_val_dec = (fun e -> e)
      ; def_val_aux = (fun (defval,_) -> defval)
      ; pat_exp = (fun (_,e) -> e)
      ; pat_aux = (fun (pexp,_) -> pexp)
      ; lB_val_explicit = (fun (_,_,e) -> e)
      ; lB_val_implicit = (fun (_,e) -> e)
      ; lB_aux = (fun (lb,_) -> lb)
      ; pat_alg = id_pat_alg
      } exp in
  dedup eqidtyp updates

let swaptyp t (l,(Base ((t_params,_),tag,nexps,eff,effsum,bounds))) = 
  (l,Base ((t_params,t),tag,nexps,eff,effsum,bounds))

let mktup l es =
  match es with
  | [] -> E_aux (E_lit (L_aux (L_unit,Parse_ast.Generated l)),(Parse_ast.Generated l,simple_annot unit_t))
  | [e] -> e
  | _ -> 
     let effs =
       List.fold_left (fun acc e -> union_effects acc (get_effsum_exp e)) {effect = Eset []} es in
     let typs = List.map get_type es in
     E_aux (E_tuple es,(Parse_ast.Generated l,simple_annot_efr {t = Ttup typs} effs))

let mktup_pat l es =
  match es with
  | [] -> P_aux (P_wild,(Parse_ast.Generated l,simple_annot unit_t))
  | [E_aux (E_id id,_) as exp] ->
     P_aux (P_id id,(Parse_ast.Generated l,simple_annot (get_type exp)))
  | _ ->
     let typs = List.map get_type es in
     let pats = List.map (fun (E_aux (E_id id,_) as exp) ->
                    P_aux (P_id id,(Parse_ast.Generated l,simple_annot (get_type exp)))) es in
     P_aux (P_tup pats,(Parse_ast.Generated l,simple_annot {t = Ttup typs}))


type 'a updated_term =
  | Added_vars of 'a exp * 'a pat
  | Same_vars of 'a exp

let rec rewrite_var_updates ((E_aux (expaux,((l,_) as annot))) as exp) =

  let rec add_vars overwrite ((E_aux (expaux,annot)) as exp) vars =
    match expaux with
    | E_let (lb,exp) ->
       let exp = add_vars overwrite exp vars in
       E_aux (E_let (lb,exp),swaptyp (get_type exp) annot)
    | E_internal_let (lexp,exp1,exp2) ->
       let exp2 = add_vars overwrite exp2 vars in
       E_aux (E_internal_let (lexp,exp1,exp2), swaptyp (get_type exp2) annot)
    | E_internal_plet (pat,exp1,exp2) ->
       let exp2 = add_vars overwrite exp2 vars in
       E_aux (E_internal_plet (pat,exp1,exp2), swaptyp (get_type exp2) annot)
    | E_internal_return exp2 ->
       let exp2 = add_vars overwrite exp2 vars in
       E_aux (E_internal_return exp2,swaptyp (get_type exp2) annot)
    | _ ->
       (* after rewrite_defs_letbind_effects there cannot be terms that have
          effects/update local variables in "tail-position": check n_exp_term
          and where it is used. *)
       if overwrite then
         (* let () = if get_type exp = {t = Tid "unit"} then ()
                  else failwith "nono" in *)
         vars
       else
         E_aux (E_tuple [exp;vars],swaptyp {t = Ttup [get_type exp;get_type vars]} annot) in
  
  let rewrite (E_aux (expaux,((el,_) as annot))) (P_aux (_,(pl,pannot)) as pat) =
    let overwrite = match get_type_annot annot with
      | {t = Tid "unit"} -> true
      | _ -> false in
    match expaux with
    | E_for(id,exp1,exp2,exp3,order,exp4) ->
       let vars = List.map (fun (var,(l,t)) -> E_aux (E_id var,(l,t))) (find_updated_vars exp4) in
       let vartuple = mktup el vars in
       let exp4 = rewrite_var_updates (add_vars overwrite exp4 vartuple) in
       let fname = match effectful exp4,order with
         | false, Ord_aux (Ord_inc,_) -> "foreach_inc"
         | false, Ord_aux (Ord_dec,_) -> "foreach_dec"
         | true,  Ord_aux (Ord_inc,_) -> "foreachM_inc"
         | true,  Ord_aux (Ord_dec,_) -> "foreachM_dec"
         | _ -> failwith "E_for: unhandled order"
       in
       let funcl = Id_aux (Id fname,Parse_ast.Generated el) in
       let loopvar =
         let (bf,tf) = match get_type exp1 with
           | {t = Tapp ("atom",[TA_nexp f])} -> (TA_nexp f,TA_nexp f)
           | {t = Tapp ("reg", [TA_typ {t = Tapp ("atom",[TA_nexp f])}])} -> (TA_nexp f,TA_nexp f)
           | {t = Tapp ("range",[TA_nexp bf;TA_nexp tf])} -> (TA_nexp bf,TA_nexp tf)
           | {t = Tapp ("reg", [TA_typ {t = Tapp ("range",[TA_nexp bf;TA_nexp tf])}])} -> (TA_nexp bf,TA_nexp tf)
           | {t = Tapp (name,_)} -> failwith (name ^ " shouldn't be here (from) at " ^ Reporting_basic.loc_to_string el)
           | _ -> failwith "E_for: unhandled from-expr"
         in
         let (bt,tt) = match get_type exp2 with
           | {t = Tapp ("atom",[TA_nexp t])} -> (TA_nexp t,TA_nexp t)
           | {t = Tapp ("atom",[TA_typ {t = Tapp ("atom", [TA_nexp t])}])} -> (TA_nexp t,TA_nexp t)
           | {t = Tapp ("range",[TA_nexp bt;TA_nexp tt])} -> (TA_nexp bt,TA_nexp tt)
           | {t = Tapp ("atom",[TA_typ {t = Tapp ("range",[TA_nexp bt;TA_nexp tt])}])} -> (TA_nexp bt,TA_nexp tt)
           | {t = Tapp (name,_)} -> failwith (name ^ " shouldn't be here (to) at " ^ Reporting_basic.loc_to_string el)
           | _ -> failwith "E_for: unhandled to-expr"
         in
         let t = {t = Tapp ("range",match order with
                                    | Ord_aux (Ord_inc,_) -> [bf;tt]
                                    | Ord_aux (Ord_dec,_) -> [tf;bt]
                                    | _ -> failwith "E_for: unhandled Ord"
                                    )} in
         E_aux (E_id id,(Parse_ast.Generated el,simple_annot t)) in
       let v = E_aux (E_app (funcl,[loopvar;mktup el [exp1;exp2;exp3];exp4;vartuple]),
                      (Parse_ast.Generated el,simple_annot_efr (get_type exp4) (get_effsum_exp exp4))) in
       let pat =
         if overwrite then mktup_pat el vars
         else P_aux (P_tup [pat; mktup_pat pl vars],
                     (Parse_ast.Generated pl,simple_annot (get_type v))) in
       Added_vars (v,pat)
    | E_if (c,e1,e2) ->
       let vars = List.map (fun (var,(l,t)) -> E_aux (E_id var,(l,t)))
                           (dedup eqidtyp (find_updated_vars e1 @ find_updated_vars e2)) in
       if vars = [] then
         (Same_vars (E_aux (E_if (c,rewrite_var_updates e1,rewrite_var_updates e2),annot)))
       else
         let vartuple = mktup el vars in
         let e1 = rewrite_var_updates (add_vars overwrite e1 vartuple) in
         let e2 = rewrite_var_updates (add_vars overwrite e2 vartuple) in
         (* after rewrite_defs_letbind_effects c has no variable updates *)
         let t = get_type e1 in
         let v = E_aux (E_if (c,e1,e2), (Parse_ast.Generated el,simple_annot_efr t (eff_union_exps [e1;e2]))) in
         let pat =
           if overwrite then mktup_pat el vars
           else P_aux (P_tup [pat; mktup_pat pl vars],
                       (Parse_ast.Generated pl,simple_annot (get_type v))) in
         Added_vars (v,pat)
    | E_case (e1,ps) ->
       (* after rewrite_defs_letbind_effects e1 needs no rewriting *)
       let vars =
                 let f acc (Pat_aux (Pat_exp (_,e),_)) = acc @ find_updated_vars e in
         List.map (fun (var,(l,t)) -> E_aux (E_id var,(l,t)))
                  (dedup eqidtyp (List.fold_left f [] ps)) in
       if vars = [] then
         let ps = List.map (fun (Pat_aux (Pat_exp (p,e),a)) -> Pat_aux (Pat_exp (p,rewrite_var_updates e),a)) ps in
         Same_vars (E_aux (E_case (e1,ps),annot))
       else
         let vartuple = mktup el vars in
         let typ = 
           let (Pat_aux (Pat_exp (_,first),_)) = List.hd ps in
           get_type first in
         let (ps,typ,effs) =
           let f (acc,typ,effs) (Pat_aux (Pat_exp (p,e),pannot)) =
             let etyp = get_type e in
             let () = assert (simple_annot etyp = simple_annot typ) in
             let e = rewrite_var_updates (add_vars overwrite e vartuple) in
             let pannot = (Parse_ast.Generated pl,simple_annot (get_type e)) in
             let effs = union_effects effs (get_effsum_exp e) in
             let pat' = Pat_aux (Pat_exp (p,e),pannot) in
             (acc @ [pat'],typ,effs) in
           List.fold_left f ([],typ,{effect = Eset []}) ps in
         let v = E_aux (E_case (e1,ps), (Parse_ast.Generated pl,simple_annot_efr typ effs)) in
         let pat =
           if overwrite then mktup_pat el vars
           else P_aux (P_tup [pat; mktup_pat pl vars],
                       (Parse_ast.Generated pl,simple_annot (get_type v))) in
         Added_vars (v,pat)
    | E_assign (lexp,vexp) ->
       let {effect = Eset effs} = get_effsum_annot annot in
       if not (List.exists (function BE_aux (BE_lset,_) -> true | _ -> false) effs) then
         Same_vars (E_aux (E_assign (lexp,vexp),annot))
       else 
         (match lexp with
          | LEXP_aux (LEXP_id id,annot) ->
             let pat = P_aux (P_id id,(Parse_ast.Generated pl,simple_annot (get_type vexp))) in
             Added_vars (vexp,pat)
          | LEXP_aux (LEXP_cast (_,id),annot) ->
             let pat = P_aux (P_id id,(Parse_ast.Generated pl,simple_annot (get_type vexp))) in
             Added_vars (vexp,pat)
          | LEXP_aux (LEXP_vector (LEXP_aux (LEXP_id id,((l2,_) as annot2)),i),((l1,_) as annot)) ->
             let eid = E_aux (E_id id,(Parse_ast.Generated l2,simple_annot (get_type_annot annot2))) in
             let vexp = E_aux (E_vector_update (eid,i,vexp),
                               (Parse_ast.Generated l1,simple_annot (get_type_annot annot))) in
             let pat = P_aux (P_id id,(Parse_ast.Generated pl,simple_annot (get_type vexp))) in
             Added_vars (vexp,pat)
          | LEXP_aux (LEXP_vector_range (LEXP_aux (LEXP_id id,((l2,_) as annot2)),i,j),
                      ((l,_) as annot)) -> 
             let eid = E_aux (E_id id,(Parse_ast.Generated l2,simple_annot (get_type_annot annot2))) in
             let vexp = E_aux (E_vector_update_subrange (eid,i,j,vexp),
                               (Parse_ast.Generated l,simple_annot (get_type_annot annot))) in
             let pat = P_aux (P_id id,(Parse_ast.Generated pl,simple_annot (get_type vexp))) in
             Added_vars (vexp,pat)
           | _ -> failwith "E_assign: unhandled lexp"
          )
    | _ ->
       (* after rewrite_defs_letbind_effects this expression is pure and updates
       no variables: check n_exp_term and where it's used. *)
       Same_vars (E_aux (expaux,annot))  in

  match expaux with
  | E_let (lb,body) ->
     let body = rewrite_var_updates body in
     let (eff,lb) = match lb with
       | LB_aux (LB_val_implicit (pat,v),lbannot) ->
          (match rewrite v pat with
           | Added_vars (v,pat) ->
              let (E_aux (_,(l,_))) = v in
              let lbannot = (Parse_ast.Generated l,simple_annot (get_type v)) in
              (get_effsum_exp v,LB_aux (LB_val_implicit (pat,v),lbannot))
           | Same_vars v -> (get_effsum_exp v,LB_aux (LB_val_implicit (pat,v),lbannot)))
       | LB_aux (LB_val_explicit (typ,pat,v),lbannot) ->
          (match rewrite v pat with 
           | Added_vars (v,pat) ->
              let (E_aux (_,(l,_))) = v in
              let lbannot = (Parse_ast.Generated l,simple_annot (get_type v)) in
              (get_effsum_exp v,LB_aux (LB_val_implicit (pat,v),lbannot))
           | Same_vars v -> (get_effsum_exp v,LB_aux (LB_val_explicit (typ,pat,v),lbannot))) in
     let typ = simple_annot_efr (get_type body) (union_effects eff (get_effsum_exp body)) in
     E_aux (E_let (lb,body),(Parse_ast.Generated l,typ))
  | E_internal_let (lexp,v,body) ->
     (* Rewrite E_internal_let into E_let and call recursively *)
     let id = match lexp with
       | LEXP_aux (LEXP_id id,_) -> id
       | LEXP_aux (LEXP_cast (_,id),_) -> id
       | _ -> failwith "E_internal_let: unhandled lexp"
     in
     let pat = P_aux (P_id id, (Parse_ast.Generated l,simple_annot (get_type v))) in
     let lbannot = (Parse_ast.Generated l,simple_annot_efr (get_type v) (get_effsum_exp v)) in
     let lb = LB_aux (LB_val_implicit (pat,v),lbannot) in
     let exp = E_aux (E_let (lb,body),(Parse_ast.Generated l,simple_annot_efr (get_type body) (eff_union_exps [v;body]))) in
     rewrite_var_updates exp
  | E_internal_plet (pat,v,body) ->
     failwith "rewrite_var_updates: E_internal_plet shouldn't be introduced yet"
  (* There are no expressions that have effects or variable updates in
     "tail-position": check the definition nexp_term and where it is used. *)
  | _ -> exp

let replace_memwrite_e_assign exp = 
  let e_aux = fun (expaux,annot) ->
    match expaux with
    | E_assign (LEXP_aux (LEXP_memory (id,args),_),v) -> E_aux (E_app (id,args @ [v]),annot)
    | _ -> E_aux (expaux,annot) in
  fold_exp { id_exp_alg with e_aux = e_aux } exp



let remove_reference_types exp =

  let rec rewrite_t {t = t_aux} = {t = rewrite_t_aux t_aux}
  and rewrite_t_aux t_aux = match t_aux with
    | Tapp ("reg",[TA_typ {t = t_aux2}]) -> rewrite_t_aux t_aux2
    | Tapp (name,t_args) -> Tapp (name,List.map rewrite_t_arg t_args)
    | Tfn (t1,t2,imp,e) -> Tfn (rewrite_t t1,rewrite_t t2,imp,e)
    | Ttup ts -> Ttup (List.map rewrite_t ts)
    | Tabbrev (t1,t2) -> Tabbrev (rewrite_t t1,rewrite_t t2)
    | Toptions (t1,t2) ->
       let t2 = match t2 with Some t2 -> Some (rewrite_t t2) | None -> None in
       Toptions (rewrite_t t1,t2)
    | Tuvar t_uvar -> Tuvar t_uvar (*(rewrite_t_uvar t_uvar) *)
    | _ -> t_aux
(*  and rewrite_t_uvar t_uvar =
    t_uvar.subst <- (match t_uvar.subst with None -> None | Some t -> Some (rewrite_t t)) *)
  and rewrite_t_arg t_arg = match t_arg with
    | TA_typ t -> TA_typ (rewrite_t t)
    | _ -> t_arg in

  let rec rewrite_annot = function
    | NoTyp -> NoTyp
    | Base ((tparams,t),tag,nexprs,effs,effsum,bounds) ->
       Base ((tparams,rewrite_t t),tag,nexprs,effs,effsum,bounds)
    | Overload (tannot1,b,tannots) ->
       Overload (rewrite_annot tannot1,b,List.map rewrite_annot tannots) in


  fold_exp
    { id_exp_alg with 
      e_aux = (fun (e,(l,annot)) -> E_aux (e,(l,rewrite_annot annot)))
    ; lEXP_aux = (fun (lexp,(l,annot)) -> LEXP_aux (lexp,(l,rewrite_annot annot)))
    ; fE_aux = (fun (fexp,(l,annot)) -> FE_aux (fexp,(l,(rewrite_annot annot))))
    ; fES_aux = (fun (fexp,(l,annot)) -> FES_aux (fexp,(l,rewrite_annot annot)))
    ; pat_aux = (fun (pexp,(l,annot)) -> Pat_aux (pexp,(l,rewrite_annot annot)))
    ; lB_aux = (fun (lb,(l,annot)) -> LB_aux (lb,(l,rewrite_annot annot)))
    }
    exp



let rewrite_defs_remove_superfluous_letbinds =

  let rec small (E_aux (exp,_)) = match exp with
    | E_id _
    | E_lit _ -> true
    | E_cast (_,e) -> small e
    | E_list es -> List.for_all small es
    | E_cons (e1,e2) -> small e1 && small e2
    | E_sizeof _ -> true
    | _ -> false in

  let e_aux (exp,annot) = match exp with
    | E_let (lb,exp2) ->
       begin match lb,exp2 with
       (* 'let x = EXP1 in x' can be replaced with 'EXP1' *)
       | LB_aux (LB_val_explicit (_,P_aux (P_id (Id_aux (id,_)),_),exp1),_),
         E_aux (E_id (Id_aux (id',_)),_)
       | LB_aux (LB_val_explicit (_,P_aux (P_id (Id_aux (id,_)),_),exp1),_),
         E_aux (E_cast (_,E_aux (E_id (Id_aux (id',_)),_)),_)
       | LB_aux (LB_val_implicit (P_aux (P_id (Id_aux (id,_)),_),exp1),_),
         E_aux (E_id (Id_aux (id',_)),_)
       | LB_aux (LB_val_implicit (P_aux (P_id (Id_aux (id,_)),_),exp1),_),
         E_aux (E_cast (_,E_aux (E_id (Id_aux (id',_)),_)),_)
            when id = id' ->
          exp1
       (* "let x = EXP1 in return x" can be replaced with 'return (EXP1)', at
          least when EXP1 is 'small' enough *)
       | LB_aux (LB_val_explicit (_,P_aux (P_id (Id_aux (id,_)),_),exp1),_),
         E_aux (E_internal_return (E_aux (E_id (Id_aux (id',_)),_)),_)
       | LB_aux (LB_val_implicit (P_aux (P_id (Id_aux (id,_)),_),exp1),_),
         E_aux (E_internal_return (E_aux (E_id (Id_aux (id',_)),_)),_)
            when id = id' && small exp1 ->
          let (E_aux (_,e1annot)) = exp1 in
          E_aux (E_internal_return (exp1),e1annot)
       | _ -> E_aux (exp,annot) 
       end
    | _ -> E_aux (exp,annot) in

  let alg = { id_exp_alg with e_aux = e_aux } in
  rewrite_defs_base
    { rewrite_exp = (fun _ _ -> fold_exp alg)
    ; rewrite_pat = rewrite_pat
    ; rewrite_let = rewrite_let
    ; rewrite_lexp = rewrite_lexp
    ; rewrite_fun = rewrite_fun
    ; rewrite_def = rewrite_def
    ; rewrite_defs = rewrite_defs_base
    }
  

let rewrite_defs_remove_superfluous_returns =

  let has_unittype e = 
    let {t = t} = get_type e in
    t = Tid "unit" in

  let e_aux (exp,annot) = match exp with
    | E_internal_plet (pat,exp1,exp2) ->
       begin match pat,exp2 with
       | P_aux (P_lit (L_aux (lit,_)),_),
         E_aux (E_internal_return (E_aux (E_lit (L_aux (lit',_)),_)),_)
            when lit = lit' ->
          exp1
       | P_aux (P_wild,pannot),
         E_aux (E_internal_return (E_aux (E_lit (L_aux (L_unit,_)),_)),_)
            when has_unittype exp1 ->
          exp1
       | P_aux (P_id (Id_aux (id,_)),_),
         E_aux (E_internal_return (E_aux (E_id (Id_aux (id',_)),_)),_)
            when id = id' ->
          exp1
       | _ -> E_aux (exp,annot)
       end
    | _ -> E_aux (exp,annot) in

  let alg = { id_exp_alg with e_aux = e_aux } in
  rewrite_defs_base
    {rewrite_exp = (fun _ _ -> fold_exp alg)
    ; rewrite_pat = rewrite_pat
    ; rewrite_let = rewrite_let
    ; rewrite_lexp = rewrite_lexp
    ; rewrite_fun = rewrite_fun
    ; rewrite_def = rewrite_def
    ; rewrite_defs = rewrite_defs_base
    }


let rewrite_defs_remove_e_assign =
  let rewrite_exp _ _ e =
    replace_memwrite_e_assign (remove_reference_types (rewrite_var_updates e)) in
  rewrite_defs_base
    { rewrite_exp = rewrite_exp
    ; rewrite_pat = rewrite_pat
    ; rewrite_let = rewrite_let
    ; rewrite_lexp = rewrite_lexp
    ; rewrite_fun = rewrite_fun
    ; rewrite_def = rewrite_def
    ; rewrite_defs = rewrite_defs_base
    }


let rewrite_defs_lem =
  top_sort_defs >>
  rewrite_defs_remove_vector_concat >>
  rewrite_defs_exp_lift_assign >> 
  rewrite_defs_remove_blocks >> 
  rewrite_defs_letbind_effects >> 
  rewrite_defs_remove_e_assign >> 
  rewrite_defs_effectful_let_expressions >> 
  rewrite_defs_remove_superfluous_letbinds >>
  rewrite_defs_remove_superfluous_returns
  

