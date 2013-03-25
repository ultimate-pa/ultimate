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

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

public class Util {
	
	/**
	 * Check if {@code term} which may contain free {@code TermVariables} is
	 * satisfiable with respect to the current assertion stack of {@code script}.
	 * @param term may contain free variables
	 * @throws SMTLIBException 
	 */
	public static LBool checkSat(Script script, Term term) throws SMTLIBException {
		script.push(1);
		TermVariable[] vars = term.getFreeVars();
		Term[] values = new Term[vars.length];
		for (int i=0; i<vars.length; i++) {
			values[i] = termVariable2constant(script, vars[i]);
		}
		term = script.let(vars, values, term);
		script.assertTerm(term);
		LBool result = script.checkSat();
		script.pop(1);
		return result;
	}
	
	private static Term termVariable2constant(Script script, TermVariable tv) 
														throws SMTLIBException {
		String name = tv.getName() + "_const_" + tv.hashCode();
		Sort[] paramSorts = {};
		Sort resultSort = tv.getSort();
		script.declareFun(name, paramSorts, resultSort);
		Term result = script.term(name);
		return result;
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
		Term neutral = (connector.equals("and") ? script.term("true") : script.term("false"));
		List<Term> formulas = new ArrayList<Term>();
		
		for (Term f : subforms) {
			if (f == script.term("true") || f == script.term("false")) {
				if (f == neutral)
					continue;
				else
					return f;
			}

			/* Normalize nested and/ors */
			if (f instanceof ApplicationTerm
				&& ((ApplicationTerm) f).getFunction().getName().equals(connector)) {
				for (Term subf : ((ApplicationTerm) f).getParameters())
					if (!formulas.contains(subf))
						formulas.add(subf);
			} else if (!formulas.contains(f)) {
				formulas.add(f);
			}
		}
		if (formulas.size() <= 1) {
			if (formulas.isEmpty())
				return neutral;
			else
				return formulas.get(0);
		}
		Term[] arrforms = formulas.toArray(new Term[formulas.size()]);
		return script.term(connector, arrforms);
	}
	
	
	
	public static Term ite(Script script, Term cond, Term thenPart, Term elsePart) {
		if (cond == script.term("true") || thenPart == elsePart) 
			return thenPart;
		else if (cond == script.term("false")) 
			return elsePart;
		else if (thenPart == script.term("true")) 
			return Util.or(script, cond, elsePart);
		else if (elsePart == script.term("false")) 
			return Util.and(script, cond, thenPart);
		else if (thenPart == script.term("false")) 
			return Util.and(script, Util.not(script, cond), elsePart);
		else if (elsePart == script.term("true")) 
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
	
	
	public static Term implies(Script script, Term... subforms)
	{ 
		Term lastFormula = subforms[subforms.length-1];
		if (lastFormula == script.term("true")) {
			return script.term("true");
		}
		if (lastFormula == script.term("false")) {
			Term[] allButLast = new Term[subforms.length-1];
			System.arraycopy(subforms, 0, allButLast, 0, subforms.length-1);
			return Util.and(script, allButLast);
		}
		ArrayList<Term> newSubforms = new ArrayList<Term>();
		for (int i=0; i<subforms.length-1; i++) {
			if (subforms[i] == script.term("false")) {
				return script.term("true");
			}
			if (subforms[i] != script.term("true")) {
				newSubforms.add(subforms[i]);
			}
		}
		if (newSubforms.isEmpty()) {
			return lastFormula;
		}
		newSubforms.add(lastFormula);
		return script.term("=>", newSubforms.toArray(new Term[0]));
	}

}
