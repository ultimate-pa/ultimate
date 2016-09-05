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

/**
 * This class contains some static methods to help creating terms, checking
 * formulas, etc.
 * 
 * @author christ, heizmann, hoenicke 
 */
public final class Util {

	private Util() {
		// Prevent instantiation of this utility class
	}
	
	/**
	 * Check if {@code term} which may contain free {@code TermVariables} is
	 * satisfiable with respect to the current assertion stack of 
	 * {@code script}.  Only the result from this function can be used since the
	 * assertion stack will be modified after leaving this function.
	 * @param script the script used to run the check.
	 * @param term the term to check for satisfiability (possibly containing
	 *  free variables).
	 * @return the satisfiability status (SAT, UNSAT or UNKNOWN).
	 */
	public static LBool checkSat(Script script, Term term) {
		script.push(1);
		try {
			final TermVariable[] vars = term.getFreeVars();
			final Term[] values = new Term[vars.length];
			for (int i = 0; i < vars.length; i++) {
				values[i] = termVariable2constant(script, vars[i]);
			}
			term = script.let(vars, values, term);
			LBool result = script.assertTerm(term);
			if (result == LBool.UNKNOWN) {
				result = script.checkSat();
			}
			return result;
		} finally {
			script.pop(1);
		}
	}
	
	private static Term termVariable2constant(Script script, TermVariable tv) {
		final String name = tv.getName() + "_const_" + tv.hashCode();
		final Sort resultSort = tv.getSort();
		script.declareFun(name, Script.EMPTY_SORT_ARRAY, resultSort);
		return script.term(name);
	}

	/**
	 * Return slightly simplified version of (not f).  It removes
	 * double negation and simplifies (not true) and (not false).
	 * @param script the Script used to build terms.
	 * @param f the term to negate
	 * @return a term logically equivalent to (not f).
	 */
	public static Term not(Script script, Term f) {
		if (f == script.term("true")) {
			return script.term("false");
		}
		if (f == script.term("false")) {
			return script.term("true");
		}
		if (f instanceof ApplicationTerm
			&& ((ApplicationTerm)f).getFunction().getName().equals("not")) {
			return ((ApplicationTerm) f).getParameters()[0];
		}
		return script.term("not", f);
	}

	/**
	 * Return slightly simplified version of (and subforms).  It removes
	 * parameters occuring multiple times, true and false.  It also handles
	 * the case where there is only one or zero subformulas.
	 * @param script the Script used to build terms.
	 * @param subforms the sub formulas that are conjoined.
	 * @return a term logically equivalent to (and subforms).
	 */
	public static Term and(Script script, Term... subforms) {
		return simplifyAndOr(script, "and", subforms);
	}
	
	/**
	 * Return slightly simplified version of (or subforms).  It removes
	 * parameters occuring multiple times, true and false.  It also handles
	 * the case where there is only one or zero subformulas.
	 * @param script the Script used to build terms.
	 * @param subforms the sub formulas that are disjoined.
	 * @return a term logically equivalent to (or subforms).
	 */
	public static Term or(Script script, Term... subforms) {
		return simplifyAndOr(script, "or", subforms);
	}
	
	private static Term simplifyAndOr(
			Script script, String connector, Term... subforms) {
		final Term trueTerm = script.term("true");
		final Term falseTerm = script.term("false");
		Term neutral, absorbing;
		if (connector.equals("and")) {
			neutral = trueTerm;
			absorbing = falseTerm;
		} else {
			neutral = falseTerm;
			absorbing = trueTerm;
		}
		final LinkedHashSet<Term> formulas = new LinkedHashSet<Term>();
		
		for (final Term f : subforms) {
			if (f == neutral) {
				continue;
			}
			if (f == absorbing) {
				return f;
			}

			/* Normalize nested and/ors */
			if (f instanceof ApplicationTerm
				&& ((ApplicationTerm) f).getFunction().getName().equals(
						connector)) {
				for (final Term subf : ((ApplicationTerm) f).getParameters()) {
					formulas.add(subf);
				}
			} else {
				formulas.add(f);
			}
		}
		if (formulas.size() <= 1) { //NOPMD
			if (formulas.isEmpty()) {
				return neutral;
			} else {
				return formulas.iterator().next();
			}
		}
		final Term[] arrforms = formulas.toArray(new Term[formulas.size()]);
		return script.term(connector, arrforms);
	}
	
	/**
	 * Create a slightly simplified if-then-else term.  This mainly
	 * optimizes the special cases where one of the parameters is true or 
	 * false.
	 * @param script the script where the term is created.
	 * @param cond  the if condition.
	 * @param thenPart the then part.
	 * @param elsePart the else part.
	 * @return the simplified if-then-else term.
	 */
	public static Term ite(
			Script script, Term cond, Term thenPart, Term elsePart) {
		final Term trueTerm = script.term("true");
		final Term falseTerm = script.term("false");
		if (cond == trueTerm || thenPart == elsePart) {
			return thenPart;
		} else if (cond == falseTerm) {
			return elsePart;
		} else if (thenPart == trueTerm) {
			return Util.or(script, cond, elsePart);
		} else if (elsePart == falseTerm) {
			return Util.and(script, cond, thenPart);
		} else if (thenPart == falseTerm) {
			return Util.and(script, Util.not(script, cond), elsePart);
		} else if (elsePart == trueTerm) {
			return Util.or(script, Util.not(script, cond), thenPart);
		}
		return script.term("ite", cond, thenPart, elsePart);
	}

	/**
	 * Create a slightly simplified implies term.  This mainly
	 * optimizes the special cases where one of the parameters is true or 
	 * false or if a left-hand-side term occurs more than once.
	 * It also handles the case where only one subformula is given.
	 * @param script the script where the term is created.
	 * @param subforms the sub formulas.
	 * @return A simplified version of <code>(=&gt; subforms...)</code>.
	 */
	public static Term implies(Script script, Term... subforms) {
		final Term trueTerm = script.term("true");
		final Term lastFormula = subforms[subforms.length - 1];
		if (lastFormula == trueTerm) {
			return trueTerm;
		}
		final Term falseTerm = script.term("false");
		if (lastFormula == falseTerm) {
			final Term[] allButLast = new Term[subforms.length - 1];
			System.arraycopy(subforms, 0, allButLast, 0, subforms.length - 1);
			return Util.not(script, Util.and(script, allButLast));
		}
		final LinkedHashSet<Term> newSubforms = new LinkedHashSet<Term>();
		for (int i = 0; i < subforms.length - 1; i++) {
			if (subforms[i] == falseTerm) {
				return trueTerm;
			}
			if (subforms[i] != trueTerm) {
				newSubforms.add(subforms[i]);
			}
		}
		if (newSubforms.isEmpty()) {
			return lastFormula;
		}
		final Term[] newParams = newSubforms.toArray(
				new Term[newSubforms.size() + 1]);
		newParams[newParams.length - 1] = lastFormula;
		return script.term("=>", newParams);
	}
}
