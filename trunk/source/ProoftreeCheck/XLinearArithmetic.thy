(*
Title:  XLinearArithmetic.thy
Author: Christian Schilling
*)

header {* extension for linear arithmetic logic *}

theory XLinearArithmetic
imports
Real (* real numbers*)
Divides (* mod, div *)
"~~/src/HOL/TPTP/THF_Arith" (* real to int conversion *)
XBool (* propositional logic *)

begin



subsection {* additional operators *}

definition
  SMTmod :: "int => int => int"              (infixl "SMTmod" 70)
where
  SMTmod_def: "k SMTmod l = (if 0 <= l then k mod l else k mod - l)"

definition
  SMTdiv :: "int => int => int"              (infixl "SMTdiv" 70)
where
  SMTdiv_def: "k SMTdiv l = (if 0 <= l then k div l else - (k div - l))"



subsection {* Boolean operations specific to linear arithmetic *}

    (* pattern for using substitution rules without substitution
       (only used for local proofs) *)

(* normal case: not the first and not the last literal *)
lemma pattern: "[|p & s & q; s = r; p & r & q ==> False|] ==> False"
by simp

(* case for the first literal *)
lemma pattern_first: "[|q & p; q = r; r & p ==> False|] ==> False"
by simp

(* case for the last literal *)
lemma pattern_last: "[|p & q; q = r; p & r ==> False|] ==> False"
by simp


    (* de Morgan's rule with double negation *)

  (* equivalence rule (only used for local proofs) *)
  
(* 's_de_Morgan_disj_pos' already built-in as 'de_Morgan_disj' *)

lemma s_de_Morgan_disj_neg: "(~ ((~ p) | q)) = (p & (~ q))"
by simp

  (* direct rules *)

lemma de_Morgan_disj_neg: "[|p & ~((~ q) | r); p & q & (~ r) ==> False|] ==> False"
by (erule pattern_last, rule s_de_Morgan_disj_neg)

lemma de_Morgan_disj_neg_first: "[|~ ((~ p) | q); p & (~ q) ==> False|] ==> False"
by simp

lemma de_Morgan_disj_neg_last: "[|p & ~ (~ q); p & q ==> False|] ==> False"
by (erule pattern_last, rule not_not)

lemma de_Morgan_disj_pos: "[|p & ~ (q | r); p & (~ q) & (~ r) ==> False|] ==> False"
by (erule pattern_last, rule de_Morgan_disj)

lemma de_Morgan_disj_pos_first: "[|~ (p | q); (~ p) & (~ q) ==> False|] ==> False"
by simp



subsection {* multiplication of inequalities with (Farkas) coefficients *}

  (* equivalence rules (only used for local proofs) *)

(* <=, positive case *)
lemma s_farkas_pos_le: "(0::'a::linordered_idom) < c ==> (x <= 0) = (c * x <= 0)"
proof -
have lemma1: "!!a x. (0::'a::linordered_idom) < c ==> (x <= a) = (x * c <= a * c)"
by simp
assume "0 < c"
thus ?thesis
apply (subst (2) Rings.mult_zero_class.mult_zero_left [symmetric])
by (subst Groups.ab_semigroup_mult_class.mult_commute,
    subst lemma1 [where a = "0" and x = "x"], assumption, rule refl)
qed

(* <, negative case *)
lemma s_farkas_neg_less: "(c::'a::linordered_idom) < 0 ==> (~(x < 0)) = (c * x <= 0)"
proof -
assume "c < 0"
thus ?thesis
by (subst Orderings.linorder_class.not_less,
    subst (2) Rings.mult_zero_class.mult_zero_left [where a = "c", symmetric],
    subst Semiring_Normalization.comm_semiring_1_class.normalizing_semiring_rules(7),
    subst Rings.linordered_ring_strict_class.mult_le_cancel_right [where c = "c"],
    simp)
qed

 (* --- integer case --- *)

(* <=, negative case *)
lemma s_int_farkas_neg_le: "(c::int) < 0 ==> (~(x <= 0)) = (c * (x + - 1) <= 0)"
proof -
have lemma1: "!!c x y. ((x::int) < y) = (x + 1 <= y)"
by auto
have lemma2: "!!x. ((1::int) <= x) = (0 <= x - 1)"
by auto
assume "c < 0"
thus ?thesis
apply (subst Orderings.linorder_class.not_le, subst Fields.sign_simps(16),
       subst lemma1, subst Groups.comm_monoid_add_class.add_0, subst lemma2,
       subst Rings.linordered_ring_strict_class.mult_le_cancel_left_neg [symmetric],
       assumption, subst Rings.mult_zero_class.mult_zero_right)
by (rule refl)
qed

(* <, positive case *)
lemma s_int_farkas_pos_less: "(0::int) < c ==> (x < 0) = (c * (x + 1) <= 0)"
by (subst s_farkas_pos_le [symmetric], auto)

 (* --- real case --- *)

(* <=, negative case *)
lemma s_real_farkas_neg_le: "(c::real) < 0 ==> (~(x <= 0)) = (c * x < 0)"
by (subst Orderings.linorder_class.not_le, rule sym,
    subst Rings.mult_zero_class.mult_zero_right [symmetric],
    rule Rings.linordered_ring_strict_class.mult_less_cancel_left_neg)

(* <, positive case *)
lemma s_real_farkas_pos_less: "(0::real) < c ==> (x < 0) = (c * x < 0)"
by (rule iffI, erule (1) Rings.linordered_semiring_strict_class.mult_pos_neg,
    rule Rings.linordered_semiring_class.mult_left_less_imp_less,
    subst Rings.mult_zero_class.mult_zero_right, assumption,
    rule Orderings.preorder_class.less_imp_le)

  (* direct rules *)

(* <=, positive case *)
lemma farkas_pos_le: "[|p & ((x::'a::linordered_idom) <= 0) & q; 0 < c; p & (c * x <= 0) & q ==> False|] ==> False"
by (erule pattern, rule s_farkas_pos_le)

lemma farkas_pos_le_first: "[|((x::'a::linordered_idom) <= 0) & p; 0 < c; (c * x <= 0) & p ==> False|] ==> False"
by (erule pattern_first, rule s_farkas_pos_le)

lemma farkas_pos_le_last: "[|p & ((x::'a::linordered_idom) <= 0); 0 < c; p & (c * x <= 0) ==> False|] ==> False"
by (erule pattern_last, rule s_farkas_pos_le)

(* <, negative case *)
lemma farkas_neg_less: "[|p & (~((x::'a::linordered_idom) < 0)) & q; c < 0; p & (c * x <= 0) & q ==> False|] ==> False"
by (erule pattern, rule s_farkas_neg_less)

lemma farkas_neg_less_first: "[|(~((x::'a::linordered_idom) < 0)) & p; c < 0; (c * x <= 0) & p ==> False|] ==> False"
by (erule pattern_first, rule s_farkas_neg_less)

lemma farkas_neg_less_last: "[|p & (~((x::'a::linordered_idom) < 0)); c < 0; p & (c * x <= 0) ==> False|] ==> False"
by (erule pattern_last, rule s_farkas_neg_less)

(* =, only one case possible *)
lemma farkas_eq: "[|p & (x::'a::linordered_idom) = 0 & q; p & c * x <= 0 & q ==> False|] ==> False"
by simp

lemma farkas_eq_first: "[|(x::'a::linordered_idom) = 0 & p; c * x <= 0 & p ==> False|] ==> False"
by simp

lemma farkas_eq_last: "[|p & (x::'a::linordered_idom) = 0; p & c * x <= 0 ==> False|] ==> False"
by simp

 (* --- integer case --- *)

(* <=, negative case *)
lemma int_farkas_neg_le: "[|p & (~((x::int) <= 0)) & q; c < 0; p & (c * (x + - 1) <= 0) & q ==> False|] ==> False"
by (erule pattern, rule s_int_farkas_neg_le)

lemma int_farkas_neg_le_first: "[|(~((x::int) <= 0)) & p; c < 0; (c * (x + - 1) <= 0) & p ==> False|] ==> False"
by (erule pattern_first, rule s_int_farkas_neg_le)

lemma int_farkas_neg_le_last: "[|p & (~((x::int) <= 0)); c < 0; p & (c * (x + - 1) <= 0) ==> False|] ==> False"
by (erule pattern_last, rule s_int_farkas_neg_le)

(* <, positive case *)
lemma int_farkas_pos_less: "[|p & ((x::int) < 0) & q; 0 < c; p & (c * (x + 1) <= 0) & q ==> False|] ==> False"
by (erule pattern, rule s_int_farkas_pos_less)

lemma int_farkas_pos_less_first: "[|((x::int) < 0) & p; 0 < c; (c * (x + 1) <= 0) & p ==> False|] ==> False"
by (erule pattern_first, rule s_int_farkas_pos_less)

lemma int_farkas_pos_less_last: "[|p & ((x::int) < 0); 0 < c; p & (c * (x + 1) <= 0) ==> False|] ==> False"
by (erule pattern_last, rule s_int_farkas_pos_less)

 (* --- real case --- *)

(* <=, negative case *)
lemma real_farkas_neg_le: "[|p & (~((x::real) <= 0)) & q; c < 0; p & (c * x < 0) & q ==> False|] ==> False"
by (erule pattern, rule s_real_farkas_neg_le)

lemma real_farkas_neg_le_first: "[|(~((x::real) <= 0)) & p; c < 0; (c * x < 0) & p ==> False|] ==> False"
by (erule pattern_first, rule s_real_farkas_neg_le)

lemma real_farkas_neg_le_last: "[|p & (~((x::real) <= 0)); c < 0; p & (c * x < 0) ==> False|] ==> False"
by (erule pattern_last, rule s_real_farkas_neg_le)

(* <, positive case *)
lemma real_farkas_pos_less: "[|p & ((x::real) < 0) & q; 0 < c; p & (c * x < 0) & q ==> False|] ==> False"
by (erule pattern, rule s_real_farkas_pos_less)

lemma real_farkas_pos_less_first: "[|((x::real) < 0) & p; 0 < c; (c * x < 0) & p ==> False|] ==> False"
by (erule pattern_first, rule s_real_farkas_pos_less)

lemma real_farkas_pos_less_last: "[|p & ((x::real) < 0); 0 < c; p & (c * x < 0) ==> False|] ==> False"
by (erule pattern_last, rule s_real_farkas_pos_less)



subsection {* distributivity rules: c * (x + s) with c constant, x remaining sum, s last summand *}

  (* equivalence rules *)

(* summand with no factor, positive constant, positive summand *)
lemma s_dist_pos_pos: "((c::'a::linordered_idom) * (x + y)) = (c * x + c * y)"
by (rule Rings.ring_class.ring_distribs(1))

(* summand with no factor, positive constant, negative summand *)
lemma s_dist_pos_neg: "((c::'a::linordered_idom) * (x + - y)) = (c * x + - c * y)"
using s_dist_pos_pos [where c = "c"] by simp

(* summand with no factor, negative constant, positive summand *)
lemma s_dist_neg_pos: "(- (c::'a::linordered_idom) * (x + y)) = (- c * x + - c * y)"
by (rule Rings.ring_class.ring_distribs(1))

(* summand with no factor, negative constant, negative summand *)
lemma s_dist_neg_neg: "(- (c::'a::linordered_idom) * (x + - y)) = (- c * x + c * y)"
by (subst s_dist_neg_pos, subst Rings.ring_class.minus_mult_minus, rule refl)

(* summand with factor *)
lemma s_dist_factor: "(c::'a::linordered_idom) * c2 = c3 ==> (c * (x + c2 * y)) = (c * x + c3 * y)"
by (subst Rings.ring_class.ring_distribs(1), simp)

    (* normalization of remaining terms after distributivity *)

(* double negation *)
lemma s_minus_minus: "- (x::'a::linordered_idom) * - y = x * y"
by (rule Rings.ring_class.minus_mult_minus)

(* minus to front *)
lemma s_plus_minus: "(x::'a::linordered_idom) * - y = - x * y"
by simp

(* two factors *)
lemma s_factor: "(c::'a::linordered_idom) * c2 = c3 ==> (c * (c2 * x)) = (c3 * x)"
by simp

  (* direct rules *)

    (* start an equality sub-proof where substitution is safe *)

lemma dist_le: "[|p & (c::'a::linordered_idom) * x <= 0 & q; c * x = y; p & y <= 0 & q ==> False|] ==> False"
by (erule pattern [where r = "y <= 0"],
    rule cong [where x = "c * x" and y = "y"], rule refl)

lemma dist_le_first: "[|(c::'a::linordered_idom) * x <= 0 & p; c * x = y; y <= 0 & p ==> False|] ==> False"
by (erule pattern_first [where r = "y <= 0"],
    rule cong [where x = "c * x" and y = "y"], rule refl)

lemma dist_le_last: "[|p & (c::'a::linordered_idom) * x <= 0; c * x = y; p & y <= 0 ==> False|] ==> False"
by (erule pattern_last [where r = "y <= 0"],
    rule cong [where x = "c * x" and y = "y"], rule refl)

lemma dist_less: "[|p & (c::'a::linordered_idom) * x < 0 & q; c * x = y; p & y < 0 & q ==> False|] ==> False"
by (erule pattern [where r = "y < 0"],
    rule cong [where x = "c * x" and y = "y"], rule refl)

lemma dist_less_first: "[|(c::'a::linordered_idom) * x < 0 & p; c * x = y; y < 0 & p ==> False|] ==> False"
by (erule pattern_first [where r = "y < 0"],
    rule cong [where x = "c * x" and y = "y"], rule refl)

lemma dist_less_last: "[|p & (c::'a::linordered_idom) * x < 0; c * x = y; p & y < 0 ==> False|] ==> False"
by (erule pattern_last [where r = "y < 0"],
    rule cong [where x = "c * x" and y = "y"], rule refl)



subsection {* merge of two inequality literals (x < 0 & y < 0 ==> x + y < 0) *}

(* merge two literals (at least one more left) *)
lemma merge_ineqs_le_le: "[|(x::'a::linordered_idom) <= 0 & y <= 0 & q; x + y <= 0 & q ==> False|] ==> False"
by simp

lemma merge_ineqs_le_le_last: "[|(x::'a::linordered_idom) <= 0 & y <= 0; x + y <= 0 ==> False|] ==> False"
by simp

lemma merge_ineqs_le_less: "[|(x::'a::linordered_idom) <= 0 & y < 0 & q; x + y < 0 & q ==> False|] ==> False"
by simp

lemma merge_ineqs_le_less_last: "[|(x::'a::linordered_idom) <= 0 & y < 0; x + y < 0 ==> False|] ==> False"
by simp

lemma merge_ineqs_less_le: "[|(x::'a::linordered_idom) < 0 & y <= 0 & q; x + y <= 0 & q ==> False|] ==> False"
by simp

lemma merge_ineqs_less_le_last: "[|(x::'a::linordered_idom) < 0 & y <= 0; x + y < 0 ==> False|] ==> False"
by simp

lemma merge_ineqs_less_less: "[|(x::'a::linordered_idom) < 0 & y < 0 & q; x + y < 0 & q ==> False|] ==> False"
by simp

lemma merge_ineqs_less_less_last: "[|(x::'a::linordered_idom) < 0 & y < 0; x + y < 0 ==> False|] ==> False"
by simp


(* integer + real mixed *)
lemma ir_merge_ineqs_le_le: "[|(x::int) <= 0 & (y::real) <= 0 & q; x + y <= 0 & q ==> False|] ==> False"
by simp

lemma ri_merge_ineqs_le_le: "[|(x::real) <= 0 & (y::int) <= 0 & q; x + y <= 0 & q ==> False|] ==> False"
by simp

lemma ir_merge_ineqs_le_le_last: "[|(x::int) <= 0 & (y::real) <= 0; x + y <= 0 ==> False|] ==> False"
by simp

lemma ri_merge_ineqs_le_le_last: "[|(x::real) <= 0 & (y::int) <= 0; x + y <= 0 ==> False|] ==> False"
by simp

lemma ir_merge_ineqs_le_less: "[|(x::int) <= 0 & (y::real) < 0 & q; x + y < 0 & q ==> False|] ==> False"
by simp

lemma ir_merge_ineqs_le_less_last: "[|(x::int) <= 0 & (y::real) < 0; x + y < 0 ==> False|] ==> False"
by simp

lemma ri_merge_ineqs_less_le: "[|(x::real) < 0 & (y::int) <= 0 & q; x + y <= 0 & q ==> False|] ==> False"
by simp

lemma ri_merge_ineqs_less_le_last: "[|(x::real) < 0 & (y::int) <= 0; x + y < 0 ==> False|] ==> False"
by simp



subsection {* simplification of big sum after a merge of two literals *}

lemma simplify_le: "[|x <= 0 & p; x = y; y <= 0 & p ==> False|] ==> False"
by simp

lemma simplify_le_last: "[|x <= 0; x = y; y <= 0 ==> False|] ==> False"
by simp

lemma simplify_less: "[|x < 0 & p; x = y; y < 0 & p ==> False|] ==> False"
by simp

lemma simplify_less_last: "[|x < 0; x = y; y < 0 ==> False|] ==> False"
by simp



subsection {* trichotomy lemma *}

    (* main rule, disjunction must be of the order "x = 0 | x < 0 | x > 0" (elg) *)

lemma trichotomy_real: "((u::real) = 0) | (u < 0) | ~ (u <= 0)"
by auto

lemma trichotomy_int: "(y::int) = (x + 1) ==> (x = 0) | (y <= 0) | ~ (x <= 0)"
by auto



subsection {* rewriting specific lemmata *}

lemma rw_leqToLeq0: "((x::'a::linordered_idom) - y = z) ==> (x <= y) = (z <= 0)"
by auto

lemma rw_ltToLeq0: "((y::'a::linordered_idom) - x = z) ==> (x < y) = (~ (z <= 0))"
by auto

lemma rw_geqToLeq0: "((y::'a::linordered_idom) - x = z) ==> (x >= y) = (z <= 0)"
by auto

lemma rw_gtToLeq0: "((x::'a::linordered_idom) - y = z) ==> (x > y) = (~ (z <= 0))"
by auto

  (* NOTE: mod, div, and dvd are only defined for integers in SMT-LIB *)
  
lemma rw_divisible1: "(1::int) dvd x = True"
by (subst Rings.comm_semiring_1_class.one_dvd, rule refl)

lemma rw_divisible: "(x::int) ~= 0 ==> (x dvd y) = (y = (x * (y SMTdiv x)))"
by (unfold SMTdiv_def, rule iffI, unfold dvd_def, auto,
    subst Rings.ring_class.minus_mult_left, subst Divides.zmult_div_cancel,
    simp, subst Divides.ring_div_class.mod_minus_right,
    subst Divides.zminus_zmod [symmetric], simp)

lemma rw_modulo: "y ~= 0 ==> x SMTmod y = - y * (x SMTdiv y) + x"
by (unfold SMTmod_def, unfold SMTdiv_def, simp add: Divides.zmod_zdiv_equality')

lemma rw_modulo1: "x SMTmod 1 = 0"
by (simp add: SMTmod_def)

lemma rw_moduloM1: "x SMTmod - 1 = 0"
by (simp add: SMTmod_def)

lemma rw_div1: "x SMTdiv 1 = x"
by (simp add: SMTdiv_def)

lemma rw_divM1_pos: "x SMTdiv - 1 = - x"
by (simp add: SMTdiv_def)

lemma rw_divM1_neg: "(- x) SMTdiv - 1 = x"
by (simp add: SMTdiv_def)

lemma rw_divM1_fac_pos: "(c * x) SMTdiv - 1 = (- c) * x"
by (simp add: SMTdiv_def)

lemma rw_divM1_fac_neg: "((- c) * x) SMTdiv - 1 = c * x"
by (simp add: SMTdiv_def)



subsection {* tautology specific lemmata *}

(* swap for a sum in canonical form *)

lemma taut_swap_sum_bin: "(x::'a::linordered_idom) + y <= 0 ==> y + x <= 0"
by simp

lemma taut_swap_sum_ter: "~ ((x::'a::linordered_idom) + y + c <= 0) ==> ~ (y + x + c <= 0)"
by simp

(* rules for :toIntLow *)

lemma taut_toIntLow_pos1: "to_real (to_int (u::real)) + - u <= 0"
by (unfold THF_Arith.real_to_int_def, auto,
    subst Groups.ordered_ab_semigroup_add_imp_le_class.add_le_cancel_right [where c = "u", symmetric],
    auto)

lemma taut_toIntLow_pos2: "to_real (to_int (c * (u::real))) + (- c) * u <= 0"
by (subst Rings.ring_class.minus_mult_left [symmetric], rule taut_toIntLow_pos1)

lemma taut_toIntLow_neg1: "to_real (to_int (- u::real)) + u <= 0"
by (subst (2) Groups.group_add_class.minus_minus [where a = "u", symmetric],
    rule taut_toIntLow_pos1)

lemma taut_toIntLow_neg2: "to_real (to_int ((- c) * (u::real))) + c * u <= 0"
by (subst Rings.ring_class.minus_mult_left [symmetric], rule taut_toIntLow_neg1)

(* rules for :toIntHigh *)

lemma taut_toIntHigh_pos1: "~ (to_real(to_int((u::real))) + - u + 1 <= 0)"
by (unfold THF_Arith.real_to_int_def, auto, subst simp_thms(27) [symmetric],
    erule conjI [where P = "floor u + - u + 1 <= 0"],
    subst Orderings.linorder_class.not_le,
    subst Groups.ordered_ab_semigroup_add_imp_le_class.add_less_cancel_left [where c = "u - 1", symmetric],
    simp)

lemma taut_toIntHigh_pos2: "~ (to_real(to_int(c * (u::real))) + (- c) * u + 1 <= 0)"
by (subst Rings.ring_class.minus_mult_left [symmetric], rule taut_toIntHigh_pos1)

lemma taut_toIntHigh_neg1: "~ (to_real(to_int(- u::real)) + u + 1 <= 0)"
by (subst (2) Groups.group_add_class.minus_minus [where a = "u", symmetric],
    rule taut_toIntHigh_pos1)

lemma taut_toIntHigh_neg2: "~ (to_real(to_int((- c) * (u::real))) + c * u + 1 <= 0)"
by (subst Rings.ring_class.minus_mult_left [symmetric], rule taut_toIntHigh_neg1)

(* rules for :divLow *)

lemma taut_divLow_pos1: "(d::int) ~= 0 ==> d * (x SMTdiv d) + - x <= 0"
proof (cases "0 <= d")
 assume "d ~= 0"
 moreover case True
 ultimately show ?thesis
 by (unfold SMTdiv_def, auto, subst Divides.zmult_div_cancel, simp)
next
 assume "d ~= 0"
 moreover case False
 ultimately show ?thesis
 by (unfold SMTdiv_def, auto, subst Rings.ring_class.minus_mult_left,
     subst Divides.zmult_div_cancel, simp)
qed

lemma taut_divLow_pos2: "(d::int) ~= 0 ==> d * (c * x SMTdiv d) + (- c) * x <= 0"
by (subst Rings.ring_class.minus_mult_left [symmetric], rule taut_divLow_pos1)

lemma taut_divLow_neg1: "(d::int) ~= 0 ==> d * (- x SMTdiv d) + x <= 0"
by (subst (2) Groups.group_add_class.minus_minus [where a = "x", symmetric],
    rule taut_divLow_pos1)

lemma taut_divLow_neg2: "(d::int) ~= 0 ==> d * ((- c) * x SMTdiv d) + c * x <= 0"
by (subst Rings.ring_class.minus_mult_left [symmetric], rule taut_divLow_neg1)

(* rules for :divHigh *)

lemma taut_divHigh_pos1: "(d::int) ~= 0 & abs d = d2 ==> (~ d * (x SMTdiv d) + - x + d2 <= 0)"
proof (cases "d <= 0")
assume "d ~= 0 & abs d = d2"
moreover case True
ultimately show ?thesis
apply (unfold SMTdiv_def, auto)
by (subst (asm) Rings.ring_class.minus_mult_left,
    subst (asm) Divides.zmult_div_cancel, simp,
    subst (asm) (2) Groups.ordered_ab_group_add_class.neg_le_iff_le [symmetric],
    simp,
    subst simp_thms(27) [symmetric], erule conjI [where P = "- d <= x mod - d"],
    subst Orderings.linorder_class.not_le, simp)
next
assume "d ~= 0 & abs d = d2"
moreover case False
ultimately show ?thesis
apply (unfold SMTdiv_def, auto)
by (subst (asm) Orderings.linorder_class.not_le,
    subst (asm) Divides.zmult_div_cancel, simp, subst simp_thms(27) [symmetric],
    subst (asm) Groups.ordered_ab_semigroup_add_imp_le_class.add_le_cancel_left [where c = "x mod d2", symmetric],
    simp, subst simp_thms(27) [symmetric],
    erule conjI [where P = "d2 <= x mod d2"],
    subst Orderings.linorder_class.not_le, simp)
qed

lemma taut_divHigh_pos2: "(d::int) ~= 0 & abs d = d2 ==> (~ d * (c * x SMTdiv d) + (- c) * x + d2 <= 0)"
by (subst Rings.ring_class.minus_mult_left [symmetric], rule taut_divHigh_pos1)

lemma taut_divHigh_neg1: "(d::int) ~= 0 & abs d = d2 ==> (~ d * (- x SMTdiv d) + x + d2 <= 0)"
by (subst (2) Groups.group_add_class.minus_minus [where a = "x", symmetric],
    rule taut_divHigh_pos1)

lemma taut_divHigh_neg2: "(d::int) ~= 0 & abs d = d2 ==> (~ d * ((- c) * x SMTdiv d) + c * x + d2 <= 0)"
by (subst Rings.ring_class.minus_mult_left [symmetric], rule taut_divHigh_neg1)


end