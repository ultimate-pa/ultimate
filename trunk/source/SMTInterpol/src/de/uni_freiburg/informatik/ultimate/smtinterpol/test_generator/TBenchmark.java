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
package de.uni_freiburg.informatik.ultimate.smtinterpol.test_generator;

import java.io.PrintWriter;
import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleList;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

/**
 * This is a filter script around the smtlib2 benchmark solver that
 * generates verification conditions for the formula converter.  It
 * parses the formulas as usual but instead of solving them it calls
 * the generator to create verification conditions stating that the 
 * original and the converted formula are equisatisfiable.
 * 
 * @author Oday Jubran, Jochen Hoenicke
 */
public class TBenchmark extends SMTInterpol {
	Generator mGenerator;
	
	public TBenchmark(LogProxy logger, PrintWriter out) {
		super(logger);
		mGenerator = new Generator(out);
		setOption(":regular-output-channel", "stderr");
		setOption(":interactive-mode", true);
		setOption(":print-success", false);
	}

	@Override
	public void push(int n) throws SMTLIBException {
		super.push(n);
		mGenerator.addPush(n);
	}
	
	@Override
	public void pop(int n) throws SMTLIBException {
		super.pop(n);
		mGenerator.addPop(n);
	}
		
	@Override
	public LBool checkSat() throws SMTLIBException {
		generate();
		return LBool.UNKNOWN;
	}

	@Override
	public void setLogic(String logic)
	    throws UnsupportedOperationException, SMTLIBException {
		super.setLogic(Logics.valueOf(logic));
		mGenerator.setLogic(logic);
	}

	@Override
	public LBool assertTerm(Term term) throws SMTLIBException {
		final LBool result = super.assertTerm(term);
		return result;
	}

	@Override
	public void declareFun(String fun, Sort[] paramSorts, Sort resultSort) 
	    throws SMTLIBException {
		super.declareFun(fun, paramSorts, resultSort);
		mGenerator.addFuncDec(fun, paramSorts, resultSort);
	}

	@Override
	public void declareSort(String sort, int arity) throws SMTLIBException {
		super.declareSort(sort, arity);
		mGenerator.addSortDec(sort, arity);
	}

	@Override
	public void defineFun(String fun, TermVariable[] params, Sort resultSort,
			Term definition) throws SMTLIBException {
		super.defineFun(fun, params, resultSort, definition);
		mGenerator.addFuncDef(fun, params, resultSort, definition);
	}

	@Override
	public void defineSort(String sort, Sort[] params, Sort definition) 
	    throws SMTLIBException {
		super.defineSort(sort, params, definition);
		mGenerator.addSortDef(sort, params, definition);
	}
	
	@Override
	public void exit() {
		super.exit();
		mGenerator.exit();
	}
	
	public void generate() throws SMTLIBException {
    	final Term[] assertions = getAssertions();
    	final SimpleList<Clause> clauses = getEngine().getClauses();
    	final ArrayList<Clause> clauseList = new ArrayList<Clause>();
    	for (final Clause c: clauses)
		 {
			clauseList.add(c);
//    	Map<TermVariable, Term> shared = this.getConverter().getAuxVariables();
//    	generator.generate(this.getTheory(), assertions, clauseList, shared);
		}
	}
}
