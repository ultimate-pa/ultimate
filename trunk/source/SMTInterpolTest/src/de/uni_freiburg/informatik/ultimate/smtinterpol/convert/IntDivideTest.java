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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ClauseDeletionHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;

/**
 * Test Class for integer divide operators.
 *
 * @author Jochen Hoenicke
 */
public final class IntDivideTest {
	Theory mTheory;
	Clausifier mClausifier;
	Sort mIntSort, mRealSort;
	Term mI, mJ, mK, mL, mR, mS, mT;
	ArrayList<Literal[]> mClauses = new ArrayList<>();

	public IntDivideTest() {
		mTheory = new Theory(Logics.QF_UFLIRA);
		final DPLLEngine dpllEngine = new DPLLEngine(mTheory, new DefaultLogger(), () -> false);
		mClausifier = new Clausifier(dpllEngine, 0) {
			@Override
			public void addClause(final Literal[] lits, final ClauseDeletionHook hook, final ProofNode pn) {
				mClauses.add(lits);
			}
		};
		mClausifier.setLogic(Logics.QF_UFLIRA);

		final Sort[] empty = new Sort[0];
		mIntSort = mTheory.getSort("Int");
		mRealSort = mTheory.getSort("Real");
		mI = mTheory.term(mTheory.declareFunction("i", empty, mIntSort));
		mJ = mTheory.term(mTheory.declareFunction("j", empty, mIntSort));
		mK = mTheory.term(mTheory.declareFunction("k", empty, mIntSort));
		mL = mTheory.term(mTheory.declareFunction("l", empty, mIntSort));
		mR = mTheory.term(mTheory.declareFunction("r", empty, mRealSort));
		mS = mTheory.term(mTheory.declareFunction("s", empty, mRealSort));
		mT = mTheory.term(mTheory.declareFunction("t", empty, mRealSort));
	}

	@Test
	@SuppressWarnings("unused")
	public void testCreateDiv() {
		final Term five = mTheory.numeral(BigInteger.valueOf(5));// NOCHECKSTYLE
		final FunctionSymbol abs = mTheory.getFunction("abs", mIntSort);
		final FunctionSymbol add = mTheory.getFunction("+", mIntSort, mIntSort);
		final FunctionSymbol addr = mTheory.getFunction("+", mRealSort, mRealSort);
		final FunctionSymbol mul = mTheory.getFunction("*", mIntSort, mIntSort);
		final FunctionSymbol div = mTheory.getFunction("div", mIntSort, mIntSort);
		final FunctionSymbol mod = mTheory.getFunction("mod", mIntSort, mIntSort);
		final FunctionSymbol toint = mTheory.getFunction("to_int", mRealSort);
		final FunctionSymbol isint = mTheory.getFunction("is_int", mRealSort);
		final FunctionSymbol toreal = mTheory.getFunction("to_real", mIntSort);
		final Term termDiv = mTheory.term(div, mI, five);
		final Term termMod = mTheory.term(mod, mI, five);
		final Term termAbs = mTheory.term(abs, mJ);
		final Term termToI = mTheory.term(toint, mR);
		final Term termSum = mTheory.term(add, mTheory.term(mul, mTheory.term(div, mI, five), five),
				mTheory.term(mod, mI, five), mTheory.term(toint, mR), mTheory.term(abs, mJ));
		final Term formIsInt = mTheory.term(isint, mTheory.term(addr, mR, mS, mTheory.term(toreal, mI)));
		mClausifier.addFormula(formIsInt);
		System.err.println(formIsInt);
		for (final Literal[] clause : mClauses) {
			System.err.println(Arrays.toString(clause));
		}
	}
}
