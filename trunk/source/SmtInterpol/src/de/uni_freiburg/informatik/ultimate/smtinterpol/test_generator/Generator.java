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
import java.util.HashMap;
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
	private List<String> declarations;
	
	private List<Term> inputAsserts;
	private List<Term> outputAsserts;
	
	// Number of dots for new declared constant symbols
	private int dots = 1;
	
	/** Writer where the correctness conditions are written */
	PrintWriter m_out;
	
	public Generator(PrintWriter out)
	{
		declarations = new ArrayList<String>();
		inputAsserts = new ArrayList<Term>();
		outputAsserts = new ArrayList<Term>();
		m_out = out;
	}
	
	public void setLogic(String lo)
	{
		String logic = "(set-logic " + lo + ")";
		m_out.println(logic);
	}
	
	public void addPush(int n)
	{
		m_out.println("(push "+n+")");
	}
	
	public void addPop(int n)
	{
		m_out.println("(pop "+n+")");
	}
	
	public void addFuncDec(String fun, Sort[] paramSorts, Sort resultSort)
	{
		updateDots(fun);
		StringBuilder result = new StringBuilder("(declare-fun ").append(fun)
			.append(" (");
		
		if (paramSorts.length != 0)
		{
			String sep = "";
			for (Sort s : paramSorts) {
				result.append(sep).append(s);
				sep = " ";
			}
		}
		
		result.append(") ").append(resultSort).append(")");
		
		m_out.println(result);
	}
	
	public void addSortDec(String sort, int arity)
	{
		updateDots(sort);
		m_out.println("(declare-sort " + sort + " " + arity + ")");
	}
	
	public void addFuncDef(String fun, TermVariable[] params, Sort resultSort,
			Term definition)
	{
		updateDots(fun);
		String result = "(define-fun " + fun + " (";
		
		if (params.length != 0)
		{
			for (TermVariable t : params)
				result += "(" + t.toString() + " " + t.getSort() + ") ";
			
			result = result.substring(0, result.length()-1);
		}
		
		result += ") " + resultSort + " " + definition +  ")";
		
		declarations.add(result);
	}
	
	public void addSortDef(String sort, Sort[] params, Sort definition)
	{
		updateDots(sort);
		String result = "(define-sort " + sort + " (";
		
		if (params.length != 0)
		{
			for (Sort s : params)
				result += s.toString() + " ";
			
			result = result.substring(0, params.length-1);
		}
		
		result += ") " + definition + ")";
		
		declarations.add(result);
	}
	
	public void addInputAssertion(Term term)
	{
		inputAsserts.add(term);
	}
	
	public void addNewDeclaration(String dec)
	{
		dec += "; new added";
		declarations.add(dec);
	}
	
	public void addOutputAssertion(Term asser)
	{
		outputAsserts.add(asser);
	}
	
	public List<Term> getInputAssertions()
	{
		return inputAsserts;
	}

	// Write output on a file
	public void writeCorrectness(Term[] auxSymbols, Term formula)
	{
		m_out.println();
		m_out.println("(push 1)");
		m_out.println("(set-info :status unsat)");
		for (Term aux: auxSymbols)
			m_out.println("(declare-fun "+aux+" () "+aux.getSort()+")");
		m_out.println("(assert " + formula.toStringDirect() + ")");
		m_out.println("(check-sat)");
		m_out.println("(pop 1)");
		m_out.flush();
	}

	public void updateDots(String con)
	{
		int i=0;
		
		for (int j=0; j<con.length(); j++)
		{
			if (con.charAt(j) == '.')
				i++;
			else break;
		}
		dots = Math.max(dots, i+1);
	}
	
	public String getDots()
	{
		StringBuilder result = new StringBuilder();
		int i = dots;
		while (i-- > 0)
			result.append(".");
		return result.toString();
	}

	public void exit() {
		m_out.println("(exit)");
		m_out.close();
	}

	// Translate Clauses to Terms
	public Term convertClauseToTerm(Theory theory, Clause cl)
	{
		Term[] literals = new Term[cl.getSize()];
		for (int i=0; i<cl.getSize(); i++)
		{
			literals[i] = cl.getLiteral(i).getSMTFormula(theory, true);
		}
		Term clause = theory.or(literals);
		return clause;
	}
	
	public void setSharedTerms(HashMap<String, Term> sterms)
	{
		for (String name : sterms.keySet())
			addSharedTerm(name, sterms.get(name));	
	}
	
	public void addSharedTerm(String name, Term smtTerm) {
	}
	
	public void generate(Theory theory, Term[] assertions, List<Clause> clauses, Map<TermVariable, Term> shared)
	{
		theory.push();
		String prefix = getDots()+"con";
		TermVariable[] tvars = new TermVariable[shared.size()];
		Term[] terms = new Term[shared.size()];
		Term[] constants = new Term[shared.size()];
		int varnr = 0;
		for (Map.Entry<TermVariable, Term> entry : shared.entrySet()) {
			Term term = entry.getValue();
			Sort sort = term.getSort();
			String conname = prefix + varnr;
			FunctionSymbol fun = theory.declareFunction(conname, new Sort[0], sort);
			tvars[varnr] = entry.getKey();
			terms[varnr] = term;
			constants[varnr] = theory.term(fun);
			varnr++;
		}
		
		Term[] clauseTerms = new ApplicationTerm[clauses.size()];
		int j=0;
		for (Clause cl : clauses) {
			clauseTerms[j++] = convertClauseToTerm(theory, cl);
		}
		
		Term clauseSetFormula    = theory.and(clauseTerms);
		Term negClauseSetFormula = theory.term("not", clauseSetFormula);
		
		// If there are no aux variables, don't create let Terms, because
		// otherwise, It will create (let () term), which is not accepted in
		// other solvers
		if (tvars.length > 0)
		{
			negClauseSetFormula = theory.let(tvars, terms, negClauseSetFormula);
			clauseSetFormula    = theory.let(tvars, constants, clauseSetFormula);
		}

		Term original = theory.and(assertions);
		Term outputFormula1 = theory.term("and", original, negClauseSetFormula);
		Term outputFormula2 = theory.term("and", clauseSetFormula, theory.term("not", original));

		writeCorrectness(new Term[0], outputFormula1);
		writeCorrectness(constants, outputFormula2);
		theory.pop();
	}
}