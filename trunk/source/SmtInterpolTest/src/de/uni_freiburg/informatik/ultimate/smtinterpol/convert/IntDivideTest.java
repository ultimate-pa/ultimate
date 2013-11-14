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


import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ClauseDeletionHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.TestCaseWithLogger;

/**
 * Test Class for integer divide operators.
 * 
 * @author Jochen Hoenicke
 */
public final class IntDivideTest extends TestCaseWithLogger {
	Theory theory;
	Clausifier clausifier;
	Sort intSort, realSort;
	Term i,j,k,l,r,s,t;
	ArrayList<Literal[]> clauses = new ArrayList<Literal[]>();
	
	public IntDivideTest() {
		theory = new Theory(Logics.QF_UFLIRA);
		Logger logger = Logger.getRootLogger();
		DPLLEngine dpllEngine = new DPLLEngine(theory, logger);
		clausifier = new Clausifier(dpllEngine, 0) {
			@Override
			public void addClause(
					Literal[] lits, ClauseDeletionHook hook, ProofNode pn) {
				clauses.add(lits);
			}
		};
		clausifier.setLogic(Logics.QF_UFLIRA);
		
		Sort[] empty = new Sort[0];
		intSort = theory.getSort("Int");
		realSort = theory.getSort("Real");
		i = theory.term(theory.declareFunction("i", empty, intSort));
		j = theory.term(theory.declareFunction("j", empty, intSort));
		k = theory.term(theory.declareFunction("k", empty, intSort));
		l = theory.term(theory.declareFunction("l", empty, intSort));
		r = theory.term(theory.declareFunction("r", empty, realSort));
		s = theory.term(theory.declareFunction("s", empty, realSort));
		t = theory.term(theory.declareFunction("t", empty, realSort));
	}
	
	@SuppressWarnings("unused")
	public void testCreateDiv() {
		Term five = theory.numeral(BigInteger.valueOf(5));
		FunctionSymbol abs = theory.getFunction("abs", intSort);
		FunctionSymbol add = theory.getFunction("+", intSort, intSort);
		FunctionSymbol addr = theory.getFunction("+", realSort, realSort);
		FunctionSymbol mul = theory.getFunction("*", intSort, intSort);
		FunctionSymbol div = theory.getFunction("div", intSort, intSort);
		FunctionSymbol mod = theory.getFunction("mod", intSort, intSort);
		FunctionSymbol toint = theory.getFunction("to_int", realSort);
		FunctionSymbol isint = theory.getFunction("is_int", realSort);
		FunctionSymbol toreal = theory.getFunction("to_real", intSort);
		Term termDiv = theory.term(div, i, five);
		Term termMod = theory.term(mod, i, five);
		Term termAbs = theory.term(abs, j);
		Term termToI = theory.term(toint, r);
		Term termSum = theory.term(add,
				theory.term(mul, theory.term(div, i, five), five),
				theory.term(mod, i, five),
				theory.term(toint, r),
				theory.term(abs, j));
		Term formIsInt = 
				theory.term(isint,
						theory.term(addr, r, s, theory.term(toreal, i)));
		clausifier.addFormula(formIsInt);
		System.err.println(formIsInt);
		for (Literal[] clause : clauses)
			System.err.println(Arrays.toString(clause));
	}
}
