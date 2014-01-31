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
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;

public class Generator {

	// All sort, function definitions and declarations
	private final List<String> mDeclarations;

	private final List<Term> mInputAsserts;
	private final List<Term> mOutputAsserts;

	// Number of dots for new declared constant symbols
	private int mDots = 1;

	/** Writer where the correctness conditions are written */
	final PrintWriter mOut;

	public Generator(PrintWriter out) {
		mDeclarations = new ArrayList<String>();
		mInputAsserts = new ArrayList<Term>();
		mOutputAsserts = new ArrayList<Term>();
		mOut = out;
	}

	public void setLogic(String lo) {
		String logic = "(set-logic " + lo + ")";
		mOut.println(logic);
	}

	public void addPush(int n) {
		mOut.println("(push " + n + ")");
	}

	public void addPop(int n) {
		mOut.println("(pop " + n + ")");
	}

	public void addFuncDec(String fun, Sort[] paramSorts, Sort resultSort) {
		updateDots(fun);
		StringBuilder result = new StringBuilder("(declare-fun ").append(fun)
				.append(" (");

		if (paramSorts.length != 0) {
			String sep = "";
			for (Sort s : paramSorts) {
				result.append(sep).append(s);
				sep = " ";
			}
		}

		result.append(") ").append(resultSort).append(')');

		mOut.println(result);
	}

	public void addSortDec(String sort, int arity) {
		updateDots(sort);
		mOut.println("(declare-sort " + sort + " " + arity + ")");
	}

	public void addFuncDef(String fun, TermVariable[] params, Sort resultSort,
			Term definition) {
		updateDots(fun);
		StringBuilder result = new StringBuilder(30);
		result.append("(define-fun ").append(fun).append(" (");

		if (params.length != 0) {
			for (TermVariable t : params)
				result.append('(').append(t).append(' ').append(t.getSort())
						.append(')');

			result.deleteCharAt(result.length() - 1);
		}

		result.append(") ").append(resultSort).append(' ').append(definition)
				.append(')');

		mDeclarations.add(result.toString());
	}

	public void addSortDef(String sort, Sort[] params, Sort definition) {
		updateDots(sort);
		StringBuilder result = new StringBuilder(30);
		result.append("(define-sort ").append(sort).append(" (");

		if (params.length != 0) {
			for (Sort s : params)
				result.append(s).append(' ');

			result.deleteCharAt(result.length() - 1);
		}

		result.append(") ").append(definition).append(')');

		mDeclarations.add(result.toString());
	}

	public void addInputAssertion(Term term) {
		mInputAsserts.add(term);
	}

	public void addNewDeclaration(String dec) {
		dec += "; new added";
		mDeclarations.add(dec);
	}

	public void addOutputAssertion(Term asser) {
		mOutputAsserts.add(asser);
	}

	public List<Term> getInputAssertions() {
		return mInputAsserts;
	}

	// Write output on a file
	public void writeCorrectness(Term[] auxSymbols, Term formula) {
		mOut.println();
		mOut.println("(push 1)");
		mOut.println("(set-info :status unsat)");
		for (Term aux : auxSymbols)
			mOut.println("(declare-fun " + aux + " () " + aux.getSort() + ")");
		mOut.println("(assert " + formula.toStringDirect() + ")");
		mOut.println("(check-sat)");
		mOut.println("(pop 1)");
		mOut.flush();
	}

	public void updateDots(String con) {
		int i = 0;

		for (int j = 0; j < con.length(); j++) {
			if (con.charAt(j) == '.')
				i++;
			else
				break;
		}
		mDots = Math.max(mDots, i + 1);
	}

	public String getDots() {
		StringBuilder result = new StringBuilder();
		int i = mDots;
		while (i-- > 0)
			result.append('.');
		return result.toString();
	}

	public void exit() {
		mOut.println("(exit)");
		mOut.close();
	}

	// Translate Clauses to Terms
	public Term convertClauseToTerm(Theory theory, Clause cl) {
		Term[] literals = new Term[cl.getSize()];
		for (int i = 0; i < cl.getSize(); i++) {
			literals[i] = cl.getLiteral(i).getSMTFormula(theory, true);
		}
		Term clause = theory.or(literals);
		return clause;
	}

	public void generate(Theory theory, Term[] assertions,
			List<Clause> clauses, Map<TermVariable, Term> shared) {
		theory.push();
		String prefix = getDots() + "con";
		TermVariable[] tvars = new TermVariable[shared.size()];
		Term[] terms = new Term[shared.size()];
		Term[] constants = new Term[shared.size()];
		int varnr = 0;
		for (Map.Entry<TermVariable, Term> entry : shared.entrySet()) {
			Term term = entry.getValue();
			Sort sort = term.getSort();
			String conname = prefix + varnr;
			FunctionSymbol fun = theory.declareFunction(conname, new Sort[0],
					sort);
			tvars[varnr] = entry.getKey();
			terms[varnr] = term;
			constants[varnr] = theory.term(fun);
			varnr++;
		}

		Term[] clauseTerms = new ApplicationTerm[clauses.size()];
		int j = 0;
		for (Clause cl : clauses) {
			clauseTerms[j++] = convertClauseToTerm(theory, cl);
		}

		Term clauseSetFormula = theory.and(clauseTerms);
		Term negClauseSetFormula = theory.term("not", clauseSetFormula);

		// If there are no aux variables, don't create let Terms, because
		// otherwise, It will create (let () term), which is not accepted in
		// other solvers
		if (tvars.length > 0) {
			negClauseSetFormula = theory.let(tvars, terms, negClauseSetFormula);
			clauseSetFormula = theory.let(tvars, constants, clauseSetFormula);
		}

		Term original = theory.and(assertions);
		Term outputFormula1 = theory.term("and", original, negClauseSetFormula);
		Term outputFormula2 = theory.term("and", clauseSetFormula,
				theory.term("not", original));

		writeCorrectness(new Term[0], outputFormula1);
		writeCorrectness(constants, outputFormula2);
		theory.pop();
	}
}
