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

module Envmap : Finite_map.Fmap with type k = string
module Nameset : sig
  include Set.S with type elt = string
  val pp : Format.formatter -> t -> unit
end

val zero : big_int
val one  : big_int
val two  : big_int

(*Trinary replacement for boolean, as sometimes we do want to distinguish we just don't know from a certain yes or no*)
type triple = Yes | No | Maybe
val triple_negate : triple -> triple

type kind = { mutable k : k_aux }
and k_aux =
  | K_Typ
  | K_Nat
  | K_Ord
  | K_Efct
  | K_Val
  | K_Lam of kind list * kind
  | K_infer

type t_uvar
type n_uvar
type e_uvar
type o_uvar
type t = { mutable t : t_aux }
(*No recursive t will ever be Tfn *)
and t_aux =
  | Tvar of string (* concrete *)
  | Tid of string  (* concrete *)
  | Tfn of t * t * implicit_parm * effect  (* concrete *)
  | Ttup of t list (* concrete *)
  | Tapp of string * t_arg list (* concrete *)
  | Tabbrev of t * t (* first t is the type from the source; second is the actual ground type, never abbrev *)
  | Toptions of t * t option (* used in overloads or cast; first is always concrete. Removed in type checking *)
  | Tuvar of t_uvar (* Unification variable *)
(*Implicit nexp parameters for library and special function calls*)
and implicit_parm =
  | IP_none (*Standard function*)
  | IP_length of nexp (*Library function to take length of a vector as first parameter*)
  | IP_start of nexp (*Library functions to take start of a vector as first parameter*)
  | IP_user of nexp (*Special user functions, must be declared with val, will pass stated parameter to function from return type*)
and nexp = { mutable nexp : nexp_aux ; mutable imp_param : bool}
and nexp_aux =
  | Nvar of string
  | Nid of string * nexp
  | Nconst of big_int
  | Npos_inf (* Used to define nat and int types, does not arise from source otherwise *)
  | Nneg_inf (* Used to define int type, does not arise from source otherwise *)
  | Nadd of nexp * nexp
  | Nsub of nexp * nexp
  | Nmult of nexp * nexp
  | N2n of nexp * big_int option (* Optionally contains the 2^n result for const n, for different constraint equations *)
  | Npow of nexp * int (* Does not appear in source *)
  | Nneg of nexp (* Does not appear in source *)
  | Ninexact (*Does not appear in source*)
  | Nuvar of n_uvar (* Unification variable *)
and effect = { mutable effect : effect_aux }
and effect_aux =
  | Evar of string
  | Eset of Ast.base_effect list
  | Euvar of e_uvar (* Unificiation variable *)
and order = { mutable order : order_aux }
and order_aux =
  | Ovar of string
  | Oinc
  | Odec
  | Ouvar of o_uvar (* Unification variable *)
and t_arg =
  | TA_typ of t
  | TA_nexp of nexp
  | TA_eft of effect
  | TA_ord of order 

module Nexpmap : Finite_map.Fmap with type k = nexp
type nexp_map = nexp Nexpmap.t

type alias_inf =
  | Alias_field of string * string
  | Alias_extract of string * int * int
  | Alias_pair of string * string

type tag =
  | Emp_local (* Standard value, variable, expression *)
  | Emp_global (* Variable from global instead of local scope *)
  | Emp_intro (* Local mutable variable, and this is its introduction *)
  | Emp_set (* Local mutable expression being set *)
  | Tuple_assign of tag list (* Tuple of assignments, should not be External, Default, Construct, etc*)
  | External of string option (* External function or register name *)
  | Default (* Variable has default type, has not been bound *)
  | Constructor of int (* Variable is a data constructor, int says how many variants are in this family *)
  | Enum of int (* Variable came from an enumeration, int tells me the highest possible numeric value *)
  | Alias of alias_inf (* Variable came from a register alias *)
  | Spec (* Variable came from a val specification *)

type constraint_origin =
  | Patt of Parse_ast.l
  | Expr of Parse_ast.l
  | Fun of Parse_ast.l
  | Specc of Parse_ast.l

type range_enforcement = Require | Guarantee 
type cond_kind = Positive | Negative | Solo | Switch
type 'a many = One of 'a | Two of 'a * 'a | Many of 'a list

(* Constraints for nexps, plus the location which added the constraint *)
type nexp_range =
  | LtEq of constraint_origin * range_enforcement * nexp * nexp
  | Lt of constraint_origin * range_enforcement * nexp * nexp
  | Eq of constraint_origin * nexp * nexp
  | NtEq of constraint_origin * nexp * nexp
  | GtEq of constraint_origin * range_enforcement * nexp * nexp
  | Gt of constraint_origin * range_enforcement * nexp * nexp
  | In of constraint_origin * string * int list
   (* InS holds the nuvar after a substitution *)
  | InS of constraint_origin * nexp * int list
  (* Predicate treats the first constraint as holding in positive condcons, the second in negative:
     must be one of LtEq, Eq, or GtEq, never In, Predicate, Cond, or Branch *)
  | Predicate of constraint_origin * nexp_range * nexp_range 
  (* Constraints from one path from a conditional (pattern or if) and the constraints from that conditional *)
  | CondCons of constraint_origin * cond_kind * (nexp Nexpmap.t) option * nexp_range list * nexp_range list 
  (* CondCons constraints from all branches of a conditional; list should be all CondCons *)
  | BranchCons of constraint_origin * ((nexp many) Nexpmap.t) option * nexp_range list

val get_c_loc : constraint_origin -> Parse_ast.l

val n_zero : nexp
val n_one : nexp
val n_two : nexp
val mk_nv : string -> nexp
val mk_nid : string -> nexp -> nexp
val mk_add : nexp -> nexp -> nexp
val mk_sub : nexp -> nexp -> nexp
val mk_mult : nexp -> nexp -> nexp
val mk_c : big_int -> nexp 
val mk_c_int : int -> nexp
val mk_neg : nexp -> nexp 
val mk_2n : nexp -> nexp 
val mk_2nc : nexp -> big_int -> nexp 
val mk_pow : nexp -> int -> nexp 
val mk_p_inf : unit -> nexp
val mk_n_inf : unit -> nexp 
val mk_inexact : unit -> nexp 
val set_imp_param : nexp -> unit

val mk_atom : nexp -> t
val mk_tup : t list -> t
val mk_vector : t -> order -> nexp -> nexp -> t

type variable_range =
  | VR_eq of string * nexp
  | VR_range of string * nexp_range list
  | VR_vec_eq of string * nexp
  | VR_vec_r of string * nexp_range list
  | VR_recheck of string * t (*For cases where inference hasn't yet determined the type of v*)

type bounds_env = 
  | No_bounds
  | Bounds of variable_range list * nexp_map option

type t_params = (string * kind) list
type tannot = 
  | NoTyp
  (*A type of a function, variable, expression, etc, that is not overloaded: 
    the first effect is for local effects to the current expression or variable
    the second effect is the cummulative effects of any contained subexpressions where applicable, pure otherwise *)
  | Base of (t_params * t) * tag * nexp_range list * effect * effect * bounds_env
  (* First tannot is the most polymorphic version; the list includes all variants. All t to be Tfn *)
  | Overload of tannot * bool * tannot list 

type 'a emap = 'a Envmap.t

type rec_kind = Record | Register
type rec_env = (string * rec_kind * tannot * ((string * t) list))
type alias_kind = OneReg of string * tannot | TwoReg of string * string * tannot | MultiReg of (string list) * tannot
type def_envs = { 
  k_env: kind emap; 
  abbrevs: tannot emap;
  nabbrevs: nexp emap;
  namesch : tannot emap; 
  enum_env : (string list) emap; 
  rec_env : rec_env list;
  alias_env : alias_kind emap;
  default_o : order;
 }

type exp = tannot Ast.exp

type minmax = (constraint_origin * nexp) option
type constraints = nexp_range list


val lookup_record_typ : string -> rec_env list -> rec_env option
val lookup_record_fields : string list -> rec_env list -> rec_env option
val lookup_possible_records : string list -> rec_env list -> rec_env list
val lookup_field_type : string -> rec_env -> t option

val add_effect : Ast.base_effect -> effect -> effect
val union_effects : effect -> effect -> effect
val e_to_string : effect -> string
val has_rreg_effect : effect -> bool
val has_wreg_effect : effect -> bool
val has_rmem_effect : effect -> bool
val has_wmem_effect : effect -> bool
val has_eamem_effect : effect -> bool
val has_memv_effect : effect -> bool
val has_lret_effect : effect -> bool
  
val initial_kind_env : kind Envmap.t
val initial_abbrev_env : tannot Envmap.t
val initial_typ_env : tannot Envmap.t
val nat_t : t
val unit_t : t
val int64_t : t
val bool_t : t
val bit_t : t
val string_t : t
val pure_e : effect
val nob : bounds_env

val simple_annot : t -> tannot
val simple_annot_efr : t -> effect -> tannot
val global_annot : t -> tannot
val tag_annot : t -> tag -> tannot
val tag_annot_efr : t -> tag -> effect -> tannot
val constrained_annot : t -> constraints -> tannot
val constrained_annot_efr : t -> constraints -> effect -> tannot
val bounds_annot : t -> bounds_env -> tannot
val bounds_annot_efr : t -> bounds_env -> effect -> tannot
val cons_tag_annot : t -> tag -> constraints -> tannot
val cons_tag_annot_efr : t -> tag -> constraints -> effect -> tannot
val cons_efl_annot : t -> constraints -> effect -> tannot
val cons_efs_annot : t -> constraints -> effect -> effect -> tannot
val efs_annot : t -> effect -> effect -> tannot
val tag_efs_annot: t -> tag -> effect -> effect -> tannot
val cons_bs_annot : t -> constraints -> bounds_env -> tannot
val cons_bs_annot_efr : t -> constraints -> bounds_env -> effect -> tannot

val kind_to_string : kind -> string
val t_to_string : t -> string
val n_to_string : nexp -> string
val constraints_to_string : constraints -> string
val bounds_to_string : bounds_env -> string
val tannot_to_string : tannot -> string
val t_to_typ : t -> Ast.typ

val int_to_nexp : int -> nexp

val reset_fresh : unit -> unit
val new_t : unit -> t
val new_n : unit -> nexp
val new_o : unit -> order
val new_e : unit -> effect
val equate_t : t -> t -> unit

val typ_subst : t_arg emap -> bool -> t -> t 
val subst : (Envmap.k * kind) list -> bool -> bool -> t -> constraints -> effect -> t * constraints * effect * t_arg emap
val subst_with_env : t_arg emap -> bool -> t -> nexp_range list -> effect -> t * constraints * effect * t_arg emap
val subst_n_with_env : t_arg emap -> nexp -> nexp
val type_param_consistent : Parse_ast.l -> t_arg emap -> t_arg emap -> nexp_range list

val get_abbrev : def_envs -> t -> (t * nexp_range list)

val is_enum_typ : def_envs -> t -> int option
val is_bit_vector : t -> bool

val extract_bounds : def_envs -> string -> t -> bounds_env
val merge_bounds : bounds_env -> bounds_env -> bounds_env
val find_var_from_nexp : nexp -> bounds_env -> (string option * string) option
val add_map_to_bounds : nexp_map -> bounds_env -> bounds_env
val add_map_tannot : nexp_map -> tannot -> tannot
val get_map_tannot : tannot -> nexp_map option
val merge_option_maps : nexp_map option -> nexp_map option -> nexp_map option

val expand_nexp : nexp -> nexp list
val normalize_nexp : nexp -> nexp
val get_index : nexp -> int (*expose nindex through this for debugging purposes*)
val get_all_nvar : nexp -> string list (*Pull out all of the contained nvar and nuvars in nexp*)

val select_overload_variant : def_envs -> bool -> bool -> tannot list -> t -> tannot list

(*splits constraints into always, positive, negative constraints; where positive and negative happen for predicates *)
val split_conditional_constraints : constraints -> (constraints * constraints * constraints)

(*May raise an exception if a contradiction is found*)
val resolve_constraints : constraints -> (constraints * nexp_map option)
(* whether to actually perform constraint resolution or not *)
val do_resolve_constraints : bool ref
val z3_solver : bool ref
                                  
(*May raise an exception if effects do not match tannot effects,
  will lift unification variables to fresh type variables *)
val check_tannot : Parse_ast.l -> tannot -> nexp option -> constraints -> effect -> tannot

val nexp_eq_check : nexp -> nexp -> bool (*structural equality only*)
val nexp_eq : nexp -> nexp -> bool
val nexp_one_more_than : nexp -> nexp -> bool

(*Selects the subset of given list where an nexp_range contains the given nexp, presumed to be an nvar*)
val contains_nvar : nexp -> constraints -> constraints
(*As above but with nuvars*)
val contains_nuvar : nexp -> constraints -> constraints
(*Removes first nexp from second nexp, when first nexp is a nuvar or nvar. 
  If it isn't possible to remove the first nexp fully and leave integral values on the resulting nexp
  i.e. if we have isolate_nexp 'i (8*i) + 3), then we return the nexp and any non-removable factors
  (this may include 2 ^^ 'x) 
*)
val isolate_nexp : nexp -> nexp -> (nexp option * nexp option * nexp)
val refine_requires: bool -> minmax -> minmax -> Nexpmap.k -> constraints -> constraints * minmax * minmax 
val refine_guarantees: bool -> minmax-> minmax -> Nexpmap.k -> constraints -> constraints * minmax * minmax


(*type relations*)

val conforms_to_t : def_envs -> bool -> bool -> t -> t -> bool

(* type_consistent is similar to a standard type equality, except in the case of [[consistent t1 t2]] where
   t1 and t2 are both range types and t1 is contained within the range of t2: i.e.
   range<2, 5> is consistent with range<0, 10>, but not vice versa.
   Similar for atom.
   When widen, two atoms are used to generate a range that contains them (or is defined by them for constants; and an atom and a range may widen the range.
   type_consistent mutates uvars to perform unification and will raise an error if the [[t1]] and [[t2]] are inconsistent
*)
val type_consistent : constraint_origin -> def_envs -> range_enforcement -> bool -> t -> t -> t * constraints

(* type_coerce mutates to unify variables, and will raise an exception if the first type cannot
   be coerced into the second and is additionally inconsistent with the second; 
   bool specifices whether this has arisen from an implicit or explicit type coercion request
   type_coerce origin envs enforce is_explicit (ie came from user) widen bounds t exp expect_t
 *)
val type_coerce : constraint_origin -> def_envs -> range_enforcement -> bool -> bool -> bounds_env -> t -> exp -> t -> t * constraints * effect * exp

(* Merge tannots when intersection or unioning two environments. In case of default types, defer to tannot on right 
   When merging atoms, use bool to control widening. 
*)
val tannot_merge : constraint_origin -> def_envs -> bool -> tannot -> tannot -> tannot 

val initial_typ_env : tannot Envmap.t

val initial_typ_env_list : (string * ((string * tannot) list)) list 

