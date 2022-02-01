/*
 * Copyright (C) 2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Just a collection of constants denoting rewrite axioms or auxiliary axioms.
 * @author Juergen Christ, Jochen Hoenicke
 */
public interface ProofConstants {

	//// ==== Proof sort and functions ====
	public final static String SORT_PROOF = "@Proof";
	public static final String FN_TAUTOLOGY = "@tautology";
	public static final String FN_REWRITE = "@rewrite";
	public static final String FN_MP = "@mp";
	public static final String FN_SPLIT = "@split";
	public static final String FN_EXISTS = "@exists";
	public static final String FN_ALLINTRO = "@allIntro";
	public static final String FN_CONG = "@cong";
	public static final String FN_ORMONOTONY = "@orMonotony";
	public static final String FN_TRANS = "@trans";
	public static final String FN_REFL = "@refl";
	public static final String FN_ASSERTED = "@asserted";
	public static final String FN_ASSUMPTION = "@assumption";
	public static final String FN_CLAUSE = "@clause";
	public static final String FN_LEMMA = "@lemma";
	public static final String FN_RES = "@res";

	//// ==== Rewrite ids and names ====
	public final static Annotation RW_EXPAND            = new Annotation(":expand", null);
	public final static Annotation RW_EXPAND_DEF        = new Annotation(":expandDef", null);
	public final static Annotation RW_TRUE_NOT_FALSE    = new Annotation(":trueNotFalse", null);
	public final static Annotation RW_CONST_DIFF        = new Annotation(":constDiff", null);
	public final static Annotation RW_EQ_TRUE           = new Annotation(":eqTrue", null);
	public final static Annotation RW_EQ_FALSE          = new Annotation(":eqFalse", null);
	public final static Annotation RW_EQ_SIMP           = new Annotation(":eqSimp", null);
	public final static Annotation RW_EQ_SAME           = new Annotation(":eqSame", null);
	public final static Annotation RW_EQ_BINARY         = new Annotation(":eqBinary", null);
	public final static Annotation RW_EQ_TO_XOR         = new Annotation(":eqToXor", null);
	public final static Annotation RW_DISTINCT_BOOL     = new Annotation(":distinctBool", null);
	public final static Annotation RW_DISTINCT_TO_XOR   = new Annotation(":distinctToXor", null);
	public final static Annotation RW_DISTINCT_SAME     = new Annotation(":distinctSame", null);
	public final static Annotation RW_DISTINCT_BINARY   = new Annotation(":distinctBinary", null);
	public final static Annotation RW_NOT_SIMP          = new Annotation(":notSimp", null);
	public final static Annotation RW_OR_SIMP           = new Annotation(":orSimp", null);
	public final static Annotation RW_OR_TAUT           = new Annotation(":orTaut", null);
	public final static Annotation RW_ITE_TRUE          = new Annotation(":iteTrue", null);
	public final static Annotation RW_ITE_FALSE         = new Annotation(":iteFalse", null);
	public final static Annotation RW_ITE_SAME          = new Annotation(":iteSame", null);
	public final static Annotation RW_ITE_BOOL_1        = new Annotation(":iteBool1", null);
	public final static Annotation RW_ITE_BOOL_2        = new Annotation(":iteBool2", null);
	public final static Annotation RW_ITE_BOOL_3        = new Annotation(":iteBool3", null);
	public final static Annotation RW_ITE_BOOL_4        = new Annotation(":iteBool4", null);
	public final static Annotation RW_ITE_BOOL_5        = new Annotation(":iteBool5", null);
	public final static Annotation RW_ITE_BOOL_6        = new Annotation(":iteBool6", null);
	public final static Annotation RW_AND_TO_OR         = new Annotation(":andToOr", null);
	public final static Annotation RW_XOR_TRUE          = new Annotation(":xorTrue", null);
	public final static Annotation RW_XOR_FALSE         = new Annotation(":xorFalse", null);
	public final static Annotation RW_XOR_NOT           = new Annotation(":xorNot", null);
	public final static Annotation RW_XOR_SAME          = new Annotation(":xorSame", null);
	public final static Annotation RW_IMP_TO_OR         = new Annotation(":impToOr", null);
	public final static Annotation RW_STRIP             = new Annotation(":strip", null);
	public final static Annotation RW_CANONICAL_SUM     = new Annotation(":canonicalSum", null);
	public final static Annotation RW_LEQ_TO_LEQ0       = new Annotation(":leqToLeq0", null);
	public final static Annotation RW_LT_TO_LEQ0        = new Annotation(":ltToLeq0", null);
	public final static Annotation RW_GEQ_TO_LEQ0       = new Annotation(":geqToLeq0", null);
	public final static Annotation RW_GT_TO_LEQ0        = new Annotation(":gtToLeq0", null);
	public final static Annotation RW_LEQ_TRUE          = new Annotation(":leqTrue", null);
	public final static Annotation RW_LEQ_FALSE         = new Annotation(":leqFalse", null);
	public final static Annotation RW_DIVISIBLE         = new Annotation(":divisible", null);
	public final static Annotation RW_MODULO            = new Annotation(":modulo", null);
	public final static Annotation RW_MODULO_ONE        = new Annotation(":modulo1", null);
	public final static Annotation RW_MODULO_MONE       = new Annotation(":modulo-1", null);
	public final static Annotation RW_MODULO_CONST      = new Annotation(":moduloConst", null);
	public final static Annotation RW_DIV_ONE           = new Annotation(":div1", null);
	public final static Annotation RW_DIV_MONE          = new Annotation(":div-1", null);
	public final static Annotation RW_DIV_CONST         = new Annotation(":divConst", null);
	public final static Annotation RW_TO_INT            = new Annotation(":toInt", null);
	public final static Annotation RW_STORE_OVER_STORE  = new Annotation(":storeOverStore", null);
	public final static Annotation RW_SELECT_OVER_STORE = new Annotation(":selectOverStore", null);
	public final static Annotation RW_FLATTEN           = new Annotation(":flatten", null);
	public final static Annotation RW_STORE_REWRITE     = new Annotation(":storeRewrite", null);
	public final static Annotation RW_FORALL_EXISTS     = new Annotation(":forallExists", null);
	public final static Annotation RW_INTERN            = new Annotation(":intern", null);

	//// ==== Tautologies ====
	public final static Annotation AUX_TRUE_NOT_FALSE    = new Annotation(":trueNotFalse", null);
	public final static Annotation AUX_OR_POS            = new Annotation(":or+", null);
	public final static Annotation AUX_OR_NEG            = new Annotation(":or-", null);
	public final static Annotation AUX_ITE_POS_1         = new Annotation(":ite+1", null);
	public final static Annotation AUX_ITE_POS_2         = new Annotation(":ite+2", null);
	public final static Annotation AUX_ITE_POS_RED       = new Annotation(":ite+red", null);
	public final static Annotation AUX_ITE_NEG_1         = new Annotation(":ite-1", null);
	public final static Annotation AUX_ITE_NEG_2         = new Annotation(":ite-2", null);
	public final static Annotation AUX_ITE_NEG_RED       = new Annotation(":ite-red", null);
	public final static Annotation AUX_XOR_POS_1         = new Annotation(":xor+1", null);
	public final static Annotation AUX_XOR_POS_2         = new Annotation(":xor+2", null);
	public final static Annotation AUX_XOR_NEG_1         = new Annotation(":xor-1", null);
	public final static Annotation AUX_XOR_NEG_2         = new Annotation(":xor-2", null);
	public final static Annotation AUX_EXCLUDED_MIDDLE_1 = new Annotation(":excludedMiddle1", null);
	public final static Annotation AUX_EXCLUDED_MIDDLE_2 = new Annotation(":excludedMiddle2", null);
	public final static Annotation AUX_TERM_ITE          = new Annotation(":termITE", null);
	public final static Annotation AUX_TERM_ITE_BOUND    = new Annotation(":termITEBound", null);
	public final static Annotation AUX_DIV_LOW           = new Annotation(":divLow", null);
	public final static Annotation AUX_DIV_HIGH          = new Annotation(":divHigh", null);
	public final static Annotation AUX_TO_INT_LOW        = new Annotation(":toIntLow", null);
	public final static Annotation AUX_TO_INT_HIGH       = new Annotation(":toIntHigh", null);
	public final static Annotation AUX_ARRAY_STORE       = new Annotation(":store", null);
	public final static Annotation AUX_ARRAY_DIFF        = new Annotation(":diff", null);

	//// ==== Structural splitting constants ====
	public final static Annotation SPLIT_NEG_OR    = new Annotation(":notOr", null);
	public final static Annotation SPLIT_POS_XOR_1 = new Annotation(":xor+1", null);
	public final static Annotation SPLIT_POS_XOR_2 = new Annotation(":xor+2", null);
	public final static Annotation SPLIT_NEG_XOR_1 = new Annotation(":xor-1", null);
	public final static Annotation SPLIT_NEG_XOR_2 = new Annotation(":xor-2", null);
	public final static Annotation SPLIT_POS_ITE_1 = new Annotation(":ite+1", null);
	public final static Annotation SPLIT_POS_ITE_2 = new Annotation(":ite+2", null);
	public final static Annotation SPLIT_NEG_ITE_1 = new Annotation(":ite-1", null);
	public final static Annotation SPLIT_NEG_ITE_2 = new Annotation(":ite-2", null);

	//// ==== Annotations with non-null value ==== //// TODO This is probably not the best place
	public static Annotation getSplitSubstAnnot(final Term[] subst) {
		return new Annotation(":subst", subst);
	}

	public static Annotation getRewriteSkolemAnnot(final Term[] skolemFuns) {
		return new Annotation(":skolem", skolemFuns);
	}

	public static Annotation getRewriteRemoveForallAnnot(final Term[] newVars) {
		return new Annotation(":removeForall", newVars); // Implication rewrite
	}
}
