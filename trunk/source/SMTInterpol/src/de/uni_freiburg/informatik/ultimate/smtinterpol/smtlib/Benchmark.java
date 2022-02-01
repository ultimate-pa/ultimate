/*
 * Copyright (C) 2009-2012 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class Benchmark {

	private final Script mScript;
	private int mFormulaNum;
	private final Map<String, Sort> mSortTranslator;
	private final Map<String, String> mFunNameTranslator;

	public Benchmark(final Script solver, final boolean disableIPol) {
		mScript = solver;
		mFormulaNum = disableIPol ? -2 : -1;// NOCHECKSTYLE
		mSortTranslator = new HashMap<String, Sort>();
		mFunNameTranslator = new HashMap<String, String>();
		mScript.setOption(":produce-proofs", true);
	}

	public void setOption(final String option, final Object value) {
		mScript.setOption(option, value);
	}

	public void note(final String s) {
		if ("Interpolation Problem starts here".equals(s)) {
			++mFormulaNum;
		}
	}

	private final void mapFuns() {
		// some benchmarks use abs/mod/div as uninterpreted functions.
		// in smtlib2 they are predefined.  We rename the functions to save
		// names.
		mFunNameTranslator.put("abs", "abs$");
		mFunNameTranslator.put("mod", "mod$");
		mFunNameTranslator.put("div", "div$");
	}

	private final void mapArith() {
		// smtlib1 used ~ for unary minus.
		mFunNameTranslator.put("~", "-");
	}

	private final String translateFunName(final String funname) {
		final String res = mFunNameTranslator.get(funname);
		return res == null ? funname : res;
	}

	public void setLogic(final String logic) {
		final Logics l = Logics.valueOf(logic);
		mScript.setLogic(l);
		switch (l) {
		case QF_AX:
			mScript.declareSort("Index", 0);
			mScript.declareSort("Element", 0);
			mSortTranslator.put("Array",
					mScript.sort("Array", mScript.sort("Index"),
							mScript.sort("Element")));
			break;
		case AUFLIRA:
		case AUFNIRA:
			final Sort array1 = mScript.sort("Array", mScript.sort("Int"),
					mScript.sort("Real"));
			mSortTranslator.put("Array1", array1);
			mSortTranslator.put("Array2", mScript.sort("Array",
					mScript.sort("Int"), array1));
			mapFuns();
			mapArith();
			break;
		case QF_AUFLIA:
		case AUFLIA:
			mSortTranslator.put("Array", mScript.sort("Array",
					mScript.sort("Int"), mScript.sort("Real")));
			//$FALL-THROUGH$
		case QF_UFLIA:
		case QF_UFLRA:
			mapFuns();
			mapArith();
			break;
		case QF_UF:
			mScript.declareSort("U", 0);
			break;
		case LRA:
		case QF_LIA:
		case QF_LRA:
		case QF_RDL:
		case QF_IDL:
			mapArith();
			break;
		default:
			break;
		}
	}

	public void setInfo(final String info, final String value) {
		mScript.setInfo(info, value);
	}

	public void declareSort(final String name) {
		mScript.declareSort(name, 0);
	}

	public void declareFun(final String name, final Sort[] paramSorts, final Sort resultSort) {
		mScript.declareFun(translateFunName(name), paramSorts, resultSort);
	}

	public Term term(final String name, final Term... params) {
		return mScript.term(translateFunName(name), params);
	}
	public Term annotateTerm(Term t, final Annotation... annots) {
		if (annots.length > 0) {
			t = mScript.annotate(t, annots);
		}
		return t;
	}
	public Term quantifier(final int quantor, final TermVariable[] vars, final Term body,
			final Term[]...patterns) {
		return mScript.quantifier(quantor, vars, body, patterns);
	}
	public Term let(final TermVariable var, final Term value, final Term body) {
		return mScript.let(new TermVariable[]{var}, new Term[]{value}, body);
	}
	public Sort sort(final String name) {
		final Sort res = mSortTranslator.get(name);
		if (res != null) {
			return res;
		}
		return mScript.sort(name);
	}
	public TermVariable variable(final String name, final Sort sort) {
		return mScript.variable(name, sort);
	}
	public Sort getBooleanSort() {
		return mScript.sort("Bool");
	}
	public void assertTerm(Term t) {
		if (mFormulaNum >= 0) {
			t = mScript.annotate(t,
					new Annotation(":named", "IP_" + mFormulaNum++));
		}
		mScript.assertTerm(t);
	}
	public Term numeral(final String num) {
		return mScript.numeral(num);
	}
	public Term decimal(final String decimal) {
		return mScript.decimal(decimal);
	}
	public Term[] check() { // NOPMD
		final LBool res = mScript.checkSat();
		if (!(mScript instanceof LoggingScript)) {
			System.out.println(res);
		}
		if (mFormulaNum > 1) {
			final Term[] partition = new Term[mFormulaNum];
			for (int i = 0; i < mFormulaNum; ++i) {
				partition[i] = mScript.term("IP_" + i);
			}
			return mScript.getInterpolants(partition);
		}
		return null;
	}
	public void close() {
		mScript.exit();
	}

	public void getProof() {
		mScript.getProof();
	}
}
