(*
Title:  XBool.thy
Author: Christian Schilling
*)

header {* extension for propositional logic *}

theory XBool
imports Main

begin



subsection {* additional operators *}

definition
  exor :: "bool => bool => bool"              (infixl "xor" 60)
where
  xor_def: "A xor B == (A & ~B) | (~A & B)"

notation (xsymbols)
  exor (infixl "\<oplus>" 60)



subsection {* resolution step with pivot *}

(* only pivots *)
lemma res_false: "[|pl; pr; (~ pl) = pr|] ==> False"
by simp

(* only C terms *)
lemma res_c: "[|p; q; (~ pl) = pr; p = (pl | c); q = (pr | c)|] ==> c"
by auto

(* only L terms *)
lemma res_l: "[|p; pr; (~ pl) = pr; p = (pl | l)|] ==> l"
by simp

(* only L and C terms *)
lemma res_lc: "[|p; q; (~ pl) = pr; p = (pl | l | c); q = (pr | c); s = (l | c)|] ==> s"
by auto

(* only L and R terms *)
lemma res_lr: "[|p; q; (~ pl) = pr; p = (pl | l); q = (pr | r); s = (l | r)|] ==> s"
by auto

(* L, C, and R terms *)
lemma res_lcr: "[|p; q; (~ pl) = pr; p = (pl | l | c); q = (pr | c | r); s = (l | c | r)|] ==> s"
by auto



subsection {* CC (congruence closure) specific lemmata *}

(* literal equivalent to False in case no positive literal is present *)
lemma cc_false: "[|p = False; p | q|] ==> q"
by simp


(* These two rules transform the big disjunction of a CC lemma of the form
   'p | ~q1 | ... | ~qn' to the form '[|q1; ...; qn|] ==> p'.
   For this purpose use the first rule (n-1) times and the second rule once. *)
lemma cc_to_asm: "[|q ==> p | r|] ==> p | ((~ q) | r)"
by simp

lemma cc_to_asm_bin: "[|q ==> p|] ==> p | (~ q)"
by auto


(* fast version of rule 'cong' where function symbols are equal
   (which is always the case for CC proofs) *)
lemma cc_cong: "x = y ==> f x = f y"
by simp



subsection {* substitution specific lemmata *}

(* substitution rule (same as 'subst', but with different parameter order) *)
lemma eq: "[|P(s); s = t|] ==> P(t)"
by simp

  (* rewriting specific lemmata *)

(* rules for :trueNotFalse *)

lemma rw_tnf_elim: "q = False ==> (p & q) = False"
by simp

lemma rw_tnf_propT_last: "((True = p) & (p = False)) = False"
by simp

lemma rw_tnf_propT: "((True = q) & r) = False ==> ((True = p) & (p = q) & r) = False"
by simp

lemma rw_tnf_nbT: "((True = False) & p) = False"
by simp

lemma rw_tnf_nbT_last: "(True = False) = False"
by simp

lemma rw_tnf_propF_last: "((False = p) & (p = True)) = False"
by simp

lemma rw_tnf_propF: " ((False = q) & r) = False ==> ((False = p) & (p = q) & r) = False"
by auto

lemma rw_tnf_nbF: "((False = True) & p) = False"
by simp

lemma rw_tnf_nbF_last: "(False = True) = False"
by simp

(* rules for :constDiff *)

lemma rw_constDiff_bin: "c ~= d ==> (c = d) = False"
by simp

lemma rw_constDiff_start: "[|c ~= d; p ==> (c = d)|] ==> p = False"
by auto

lemma rw_constDiff_elim: "[|(p & q); q ==> c = d|] ==> (c = d)"
by simp

lemma rw_constDiff_step: "[|((c = a) & p); p ==> a = d|] ==> (c = d)"
by simp

lemma rw_constDiff_fin: "((c = d) & p) ==> (c = d)"
by simp

(* rules for :eqTrue *)

lemma rw_eqTrue_merge_left: "(p & (p = q) & r) = (p & q & r)"
by auto

lemma rw_eqTrue_merge_left_bin: "(p & (p = q)) = (p & q)"
by auto

lemma rw_eqTrue_merge_right: "((p = q) & q & r) = (p & q & r)"
by auto

lemma rw_eqTrue_merge_right_bin: "((p = q) & q) = (p & q)"
by auto

(* rules for :eqFalse *)

lemma rw_eqFalse_merge_left: "((~ p) & (p = q) & r) = ((~ p) & (~ q) & r)"
by auto

lemma rw_eqFalse_merge_left_bin: "((~ p) & (p = q)) = ((~ p) & (~ q))"
by auto

lemma rw_eqFalse_merge_right: "((p = q) & (~ q) & r) = ((~ p) & (~ q) & r)"
by auto

lemma rw_eqFalse_merge_right_bin: "((p = q) & (~ q)) = ((~ p) & (~ q))"
by auto

lemma rw_eqFalse_deMorgan: "q = (~ r) ==> ((~ p) & q) = (~ (p | r))"
by simp

(* rules for :eqSame *)

lemma rw_eqSame_bin: "((a = a) & (a = a)) = True"
by simp

lemma rw_eqSame: "(p & q) = True ==> (p & p & q) = True"
by simp

(* rules for :distinctBool *)

lemma rw_distinctBool_ter: "(((p::bool) ~= q) & (p ~= r) & (q ~= r)) = False"
by auto

lemma rw_distinctBool_start: "s --> ((q::bool) ~= r) ==> ((p ~= q) & (p ~= r) & s) = False"
by auto

lemma rw_distinctBool_fin: "((p ~= q) & r) --> (p ~= q)"
by simp

lemma rw_distinctBool_elim: "q --> (r ~= s) ==> (p & q) --> (r ~= s)"
by auto

(* rules for :distinctSame *)

lemma rw_distinctSame_fin: "(a ~= a & p) = False"
by simp

lemma rw_distinctSame_fin_bin: "(a ~= a) = False"
by simp

lemma rw_distinctSame_step: "q = False ==> (p & q) = False"
by simp

(* rules for :distinctNeg *)

lemma rw_distinctNeg_tf: "(True ~= False) = True"
by simp

lemma rw_distinctNeg_ft: "(False ~= True) = True"
by simp

lemma rw_distinctNeg_pn: "(p ~= (~ p)) = True"
by simp

lemma rw_distinctNeg_np: "((~ p) ~= p) = True"
by simp

(* rules for :distinctTrue *)

lemma rw_distinctTrue_l: "(True ~= p) = (~ p)"
by simp

lemma rw_distinctTrue_r: "(p ~= True) = (~ p)"
by simp

(* rules for :distinctFalse *)

lemma rw_distinctFalse_l: "(False ~= p) = p"
by simp

lemma rw_distinctFalse_r: "(p ~= False) = p"
by simp

(* rules for :distinctBinary *)

lemma rw_distinctBinary_bin_first: "((~ p) ~= q) = ((~ (~ p)) = q)"
by simp

lemma rw_distinctBinary_bin_second: "(p ~= q) = (p = (~ q))"
by simp

lemma rw_distinctBinary_more: "p = (~ q) ==> ((a ~= b) & p) = (~ ((a = b) | q))"
by auto

(* rules for :orTaut *)

lemma rw_orTaut_elim: "r = True ==> (q | r) = True"
by simp

lemma rw_orTaut_pos: "(~ p ==> q) ==> (p | q) = True"
by auto

lemma rw_orTaut_neg: "(p ==> q) ==> ((~ p) | q) = True"
by simp

(* rules for :impToOr *)

lemma rw_impToOr_start: "p = ((~ r) --> q) ==> p = (q | r)"
by auto

lemma rw_impToOr_step: "q = ((~ r) --> s) ==> (p --> q) = ((~ ((~ p) | r)) --> s)"
by auto

lemma rw_impToOr_fin: "(p --> q) = ((~ (~ p)) --> q)"
by simp

(* rules for :flatten *)

lemma rw_flatten_par: "(p | q | r) = s ==> ((p | q) | r) = s"
by simp

lemma rw_flatten_drop: "q = r ==> (p | q) = (p | r)"
by simp

(* other rules *)

lemma rw_expand: "p = (q & r & s) ==> p = ((q & r) & s)"
by simp

lemma rw_eqBinary: "p = (~ q) ==> ((a = b) & p) = (~ ((a ~= b) | q))"
by auto

lemma rw_iteBool1: "(if c then True else False) = c"
by simp

lemma rw_iteBool2: "(if c then False else True) = (~ c)"
by simp

lemma rw_iteBool3: "(if c then True else e) = (c | e)"
by simp

lemma rw_iteBool4: "(if c then False else e) = (~ (c | (~ e)))"
by simp

lemma rw_iteBool5: "(if c then t else True) = ((~ c) | t)"
by simp

lemma rw_iteBool6: "(if c then t else False) = (~ ((~ c) | (~ t)))"
by simp

lemma rw_andToOr: "q = (~ r) ==> (p & q) = (~ ((~ p) | r))"
by simp

lemma rw_xorToDistinct: "(p xor q) = (p ~= q)"
unfolding xor_def by auto



subsection {* tautology specific lemmata *}

(* rules for :or- *)

lemma taut_orM_fin: "(p | q) | ~ p"
by auto

lemma taut_orM_fin_bin: "p | ~ p"
by simp

lemma taut_orM_flat: "(p | q | r) | ~ s ==> ((p | q) | r) | ~ s"
by simp

lemma taut_orM_intro: "q | ~ r ==> (p | q) | ~ r"
by simp

(* rules for :excludedMiddle1 *)

lemma taut_exclMid_tr: "(~ p) | (p = True)"
by simp

lemma taut_exclMid_tl: "(~ p) | (True = p)"
by simp

(* rules for :excludedMiddle2 *)

lemma taut_exclMid_fr: "p | (p = False)"
by simp

lemma taut_exclMid_fl: "p | (False = p)"
by simp

(* rules for :termITE *)

lemma taut_termITE_unroll: "(p | q) | r ==> p | q | r"
by simp

lemma taut_termITE_then: "q | (t = x) ==> ((~ p) | q) | ((if p then t else e) = x)"
by auto

lemma taut_termITE_then_last: "(~ p) | ((if p then t else e) = t)"
by auto

lemma taut_termITE_else: "q | (e = x) ==> ((~ (~ p)) | q) | ((if p then t else e) = x)"
by auto

lemma taut_termITE_else_last: "(~ (~ p)) | ((if p then t else e) = e)"
by auto

(* other rules *)

lemma taut_iteP1: "(~ (if c then t else e)) | (~ c) | t"
by simp

lemma taut_iteP2: "(~ (if c then t else e)) | c | e"
by simp

lemma taut_itePRed: "(~ (if c then t else e)) | t | e"
by simp

lemma taut_iteM1: "(if c then t else e) | (~ c) | ~ t"
by simp

lemma taut_iteM2: "(if c then t else e) | c | ~ e"
by simp

lemma taut_iteMRed: "(if c then t else e) | (~ t) | ~ e"
by simp

lemma taut_EqP1: "(p ~= q) | p | ~ q"
by auto

lemma taut_EqP2: "(p ~= q) | (~ p) | q"
by auto

lemma taut_EqM1: "(p = q) | p | q"
by auto

lemma taut_EqM2: "(p = q) | (~ p) | ~ q"
by auto



subsection {* splitting specific lemmata *}

(* rules for :notOr *)

lemma split_notOr_finL: "~ (p | q) ==> ~ p"
by simp

lemma split_notOr_finR: "~ (p | q) ==> ~ q"
by simp

lemma split_notOr_elim: "[|~ (p | q); ~ q ==> r|] ==> r"
by simp

(* other rules *)

lemma split_eqP1: "p = q ==> p | ~ q"
by simp

lemma split_eqP2: "p = q ==> (~ p) | q"
by simp

lemma split_eqM1: "p ~= q ==> p | q"
by simp

lemma split_eqM2: "p ~= q ==> (~ p) | ~ q"
by simp

lemma split_iteP1: "if c then t else e ==> (~ c) | t"
by simp

lemma split_iteP2: "if c then t else e ==> c | e"
by (subst (asm) if_bool_eq_disj, rule disjE, auto)

lemma split_iteM1: "~ (if c then t else e) ==> (~ c) | ~ t"
by auto

lemma split_iteM2: "~ (if c then t else e) ==> c | ~ e"
by auto


end