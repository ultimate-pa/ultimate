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
package de.uni_freiburg.informatik.ultimate.logic;

import java.util.LinkedHashSet;

import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

public class Util {
	
	private static Sort[] EMPTY_SORT_ARRAY = {};
	
	/**
	 * Check if {@code term} which may contain free {@code TermVariables} is
	 * satisfiable with respect to the current assertion stack of 
	 * {@code script}.  Only the result from this function can be used since the
	 * assertion stack will be modified after leaving this function.
	 * @param term may contain free variables
	 */
	public static LBool checkSat(Script script, Term term) {
		script.push(1);
		try {
			TermVariable[] vars = term.getFreeVars();
			Term[] values = new Term[vars.length];
			for (int i=0; i<vars.length; i++)
				values[i] = termVariable2constant(script, vars[i]);
			term = script.let(vars, values, term);
			script.assertTerm(term);
			LBool result = script.checkSat();
			return result;
		} finally {
			script.pop(1);
		}
	}
	
	private static Term termVariable2constant(Script script, TermVariable tv) {
		String name = tv.getName() + "_const_" + tv.hashCode();
		Sort resultSort = tv.getSort();
		script.declareFun(name, EMPTY_SORT_ARRAY, resultSort);
		return script.term(name);
	}
	
	
	/**
	 * Return slightly simplified version of a negation.
	 */
	public static Term not(Script script, Term f)
	{
		if (f == script.term("true")) return script.term("false");
		if (f == script.term("false")) return script.term("true");
		if (f instanceof ApplicationTerm
			&& ((ApplicationTerm)f).getFunction().getName().equals("not"))
			return ((ApplicationTerm) f).getParameters()[0];
		return script.term("not", f);
	}

	/**
	 * Return slightly simplified version of a conjunction.
	 */
	public static Term and(Script script, Term... subforms) {
		return simplifyAndOr(script, "and", subforms);
	}
	
	/**
	 * Return slightly simplified version of a disjunction.
	 */
	public static Term or(Script script, Term... subforms) {
		return simplifyAndOr(script, "or", subforms);
	}
	
	private static Term simplifyAndOr(Script script, String connector, Term... subforms)
	{
		Term trueTerm = script.term("true");
		Term falseTerm = script.term("false");
		Term neutral, absorbing;
		if (connector.equals("and")) {
			neutral = trueTerm;
			absorbing = falseTerm;
		} else {
			neutral = falseTerm;
			absorbing = trueTerm;
		}
		LinkedHashSet<Term> formulas = new LinkedHashSet<Term>();
		
		for (Term f : subforms) {
			if (f == neutral)
				continue;
			if (f == absorbing)
				return f;

			/* Normalize nested and/ors */
			if (f instanceof ApplicationTerm
				&& ((ApplicationTerm) f).getFunction().getName().equals(connector)) {
				for (Term subf : ((ApplicationTerm) f).getParameters())
					formulas.add(subf);
			} else
				formulas.add(f);
		}
		if (formulas.size() <= 1) {
			if (formulas.isEmpty())
				return neutral;
			else
				return formulas.iterator().next();
		}
		Term[] arrforms = formulas.toArray(new Term[formulas.size()]);
		return script.term(connector, arrforms);
	}
	
	
	
	public static Term ite(Script script, Term cond, Term thenPart, Term elsePart) {
		Term trueTerm = script.term("true");
		Term falseTerm = script.term("false");
		if (cond == trueTerm || thenPart == elsePart) 
			return thenPart;
		else if (cond == falseTerm) 
			return elsePart;
		else if (thenPart == trueTerm) 
			return Util.or(script, cond, elsePart);
		else if (elsePart == falseTerm) 
			return Util.and(script, cond, thenPart);
		else if (thenPart == falseTerm) 
			return Util.and(script, Util.not(script, cond), elsePart);
		else if (elsePart == trueTerm)
			return Util.or(script, Util.not(script, cond), thenPart);
		return script.term("ite", cond, thenPart, elsePart);
	}
	

//	/**
//	 * Return slightly simplified version of an implication.
//	 */
//	public static Term implies(Script script, Term f, Term g)
//	{ 
//		if (g == script.term("true") || f == script.term("true")) return g;
//		if (f == script.term("false")) return script.term("true");
//		if (g == script.term("false")) return not(script, f);
//		if( f == g ) return script.term("true");
//		return script.term("=>", f, g);
//	}
	
	
	public static Term implies(Script script, Term... subforms)	{
		Term trueTerm = script.term("true");
		Term falseTerm = script.term("false");
		Term lastFormula = subforms[subforms.length-1];
		if (lastFormula == trueTerm)
			return trueTerm;
		if (lastFormula == falseTerm) {
			Term[] allButLast = new Term[subforms.length-1];
			System.arraycopy(subforms, 0, allButLast, 0, subforms.length-1);
			return Util.not(script, Util.and(script, allButLast));
		}
		LinkedHashSet<Term> newSubforms = new LinkedHashSet<Term>();
		for (int i=0; i<subforms.length-1; i++) {
			if (subforms[i] == falseTerm)
				return trueTerm;
			if (subforms[i] != trueTerm)
				newSubforms.add(subforms[i]);
		}
		if (newSubforms.isEmpty())
			return lastFormula;
		Term[] newParams = newSubforms.toArray(
				new Term[newSubforms.size() + 1]);
		newParams[newParams.length - 1] = lastFormula;
		return script.term("=>", newParams);
	}

}
