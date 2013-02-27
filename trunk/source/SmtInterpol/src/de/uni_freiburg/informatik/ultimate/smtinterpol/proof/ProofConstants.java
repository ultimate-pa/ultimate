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

/**
 * Just a collection of constants denoting rewrite axioms or auxiliary axioms.
 * @author Juergen Christ
 */
public interface ProofConstants {
	
	//// ==== Rewrite ids and names ====
	public final static int RW_EXPAND            =  0;
	public final static int RW_EXPAND_DEF        =  1;
	public final static int RW_TRUE_NOT_FALSE    =  2;
	public final static int RW_CONST_DIFF        =  3;
	public final static int RW_EQ_TRUE           =  4;
	public final static int RW_EQ_FALSE          =  5;
	public final static int RW_EQ_SIMP           =  6;
	public final static int RW_EQ_BINARY         =  7;
	public final static int RW_DISTINCT_BOOL     =  8;
	public final static int RW_DISTINCT_SAME     =  9;
	public final static int RW_DISTINCT_NEG      = 10;
	public final static int RW_DISTINCT_TRUE     = 11;
	public final static int RW_DISTINCT_FALSE    = 12;
	public final static int RW_DISTINCT_BINARY   = 13;
	public final static int RW_NOT_SIMP          = 14;
	public final static int RW_OR_SIMP           = 15;
	public final static int RW_OR_TAUT           = 16;
	public final static int RW_ITE_TRUE          = 17;
	public final static int RW_ITE_FALSE         = 18;
	public final static int RW_ITE_SAME          = 19;
	public final static int RW_ITE_BOOL_1        = 20;
	public final static int RW_ITE_BOOL_2        = 21;
	public final static int RW_ITE_BOOL_3        = 22;
	public final static int RW_ITE_BOOL_4        = 23;
	public final static int RW_ITE_BOOL_5        = 24;
	public final static int RW_ITE_BOOL_6        = 25;
	public final static int RW_AND_TO_OR         = 26;
	public final static int RW_XOR_TO_DISTINCT   = 27;
	public final static int RW_IMP_TO_OR         = 28;
	public final static int RW_STRIP             = 29;
	public final static int RW_CANONICAL_SUM     = 30;
	public final static int RW_LEQ_TO_LEQ0       = 31;
	public final static int RW_LT_TO_LEQ0        = 32;
	public final static int RW_GEQ_TO_LEQ0       = 33;
	public final static int RW_GT_TO_LEQ0        = 34;
	public final static int RW_LEQ_TRUE          = 35;
	public final static int RW_LEQ_FALSE         = 36;
	public final static int RW_DESUGAR           = 37;
	public final static int RW_DIVISIBLE         = 38;
	public final static int RW_MODULO            = 39;
	public final static int RW_MODULO_ONE        = 40;
	public final static int RW_MODULO_MONE       = 41;
	public final static int RW_MODULO_CONST      = 42;
	public final static int RW_DIV_ONE           = 43;
	public final static int RW_DIV_MONE          = 44;
	public final static int RW_DIV_CONST         = 45;
	public final static int RW_TO_INT            = 46;
	public final static int RW_EQ_SAME           = 47;
	public final static int RW_STORE_OVER_STORE  = 48;
	public final static int RW_SELECT_OVER_STORE = 49;
	public final static int RW_FLATTEN           = 50;
	
	public final static Annotation[] REWRITEANNOTS = {
		new Annotation(":expand", null),
		new Annotation(":expandDef", null),
		new Annotation(":trueNotFalse", null),
		new Annotation(":constDiff", null),
		new Annotation(":eqTrue", null),
		new Annotation(":eqFalse", null),
		new Annotation(":eqSimp", null),
		new Annotation(":eqBinary", null),
		new Annotation(":distinctBool", null),
		new Annotation(":distinctSame", null),
		new Annotation(":distinctNeg", null),
		new Annotation(":distinctTrue", null),
		new Annotation(":distinctFalse", null),
		new Annotation(":distinctBinary", null),
		new Annotation(":notSimp", null),
		new Annotation(":orSimp", null),
		new Annotation(":orTaut", null),
		new Annotation(":iteTrue", null),
		new Annotation(":iteFalse", null),
		new Annotation(":iteSame", null),
		new Annotation(":iteBool1", null),
		new Annotation(":iteBool2", null),
		new Annotation(":iteBool3", null),
		new Annotation(":iteBool4", null),
		new Annotation(":iteBool5", null),
		new Annotation(":iteBool6", null),
		new Annotation(":andToOr", null),
		new Annotation(":xorToDistinct", null),
		new Annotation(":impToOr", null),
		new Annotation(":strip", null),
		new Annotation(":canonicalSum", null),
		new Annotation(":leqToLeq0", null),
		new Annotation(":ltToLeq0", null),
		new Annotation(":geqToLeq0", null),
		new Annotation(":gtToLeq0", null),
		new Annotation(":leqTrue", null),
		new Annotation(":leqFalse", null),
		new Annotation(":desugar", null),
		new Annotation(":divisible", null),
		new Annotation(":modulo", null),
		new Annotation(":modulo1", null),
		new Annotation(":modulo-1", null),
		new Annotation(":moduloConst", null),
		new Annotation(":div1", null),
		new Annotation(":div-1", null),
		new Annotation(":divConst", null),
		new Annotation(":toInt", null),
		new Annotation(":eqSame", null),
		new Annotation(":storeOverStore", null),
		new Annotation(":selectOverStore", null),
		new Annotation(":flatten", null)
	};
	
	//// ==== Aux ids and names ====
	public final static int AUX_TRUE_NOT_FALSE    =  0;
	public final static int AUX_OR_POS            =  1;
	public final static int AUX_OR_NEG            =  2;
	public final static int AUX_ITE_POS_1         =  3;
	public final static int AUX_ITE_POS_2         =  4;
	public final static int AUX_ITE_POS_RED       =  5;
	public final static int AUX_ITE_NEG_1         =  6;
	public final static int AUX_ITE_NEG_2         =  7;
	public final static int AUX_ITE_NEG_RED       =  8;
	public final static int AUX_EQ_POS_1          =  9;
	public final static int AUX_EQ_POS_2          = 10;
	public final static int AUX_EQ_NEG_1          = 11;
	public final static int AUX_EQ_NEG_2          = 12;
	public final static int AUX_EXCLUDED_MIDDLE_1 = 13;
	public final static int AUX_EXCLUDED_MIDDLE_2 = 14;
	public final static int AUX_TERM_ITE          = 15;
	public final static int AUX_DIV_LOW           = 16;
	public final static int AUX_DIV_HIGH          = 17;
	public final static int AUX_TO_INT_LOW        = 18;
	public final static int AUX_TO_INT_HIGH       = 19;
	public final static int AUX_EQ                = 20;
	
	public final static Annotation[] AUXANNOTS = {
		new Annotation(":trueNotFalse", null),
		new Annotation(":or+", null),
		new Annotation(":or-", null),
		new Annotation(":ite+1", null),
		new Annotation(":ite+2", null),
		new Annotation(":ite+red", null),
		new Annotation(":ite-1", null),
		new Annotation(":ite-2", null),
		new Annotation(":ite-red", null),
		new Annotation(":=+1", null),
		new Annotation(":=+2", null),
		new Annotation(":=-1", null),
		new Annotation(":=-2", null),
		new Annotation(":excludedMiddle1", null),
		new Annotation(":excludedMiddle2", null),
		new Annotation(":termITE", null),
		new Annotation(":divLow", null),
		new Annotation(":divHigh", null),
		new Annotation(":toIntLow", null),
		new Annotation(":toIntHigh", null),
		new Annotation(":eq", null)
	};
	
	//// ==== Structural splitting constants ====
	public final static int SPLIT_NEG_OR    = 0;
	public final static int SPLIT_POS_EQ_1  = 1;
	public final static int SPLIT_POS_EQ_2  = 2;
	public final static int SPLIT_NEG_EQ_1  = 3;
	public final static int SPLIT_NEG_EQ_2  = 4;
	public final static int SPLIT_POS_ITE_1 = 5;
	public final static int SPLIT_POS_ITE_2 = 6;
	public final static int SPLIT_NEG_ITE_1 = 7;
	public final static int SPLIT_NEG_ITE_2 = 8;
	
	public final static Annotation[] SPLITANNOTS = {
		new Annotation(":notOr", null),
		new Annotation(":=+1", null),
		new Annotation(":=+2", null),
		new Annotation(":=-1", null),
		new Annotation(":=-2", null),
		new Annotation(":ite+1", null),
		new Annotation(":ite+2", null),
		new Annotation(":ite-1", null),
		new Annotation(":ite-2", null)
	};
}
