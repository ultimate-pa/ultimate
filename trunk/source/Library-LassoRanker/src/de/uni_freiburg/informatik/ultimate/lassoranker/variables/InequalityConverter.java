/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.variables;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermIsNotAffineException;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.UnknownFunctionException;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;


/**
 * Generate a list of LinearInequality instances from a formula in disjunctive
 * normal form
 * 
 * @author Jan Leike
 */
public class InequalityConverter {
	
	/**
	 * Convert an atomary term that is an (in-)equality into an instance of
	 * LinearInequality
	 * @param term atomary term
	 * @returns the linear inequality
	 * @throws TermException if the input term cannot be reduced to a
	 *         LinearInequality
	 */
	private static LinearInequality convertAtom(ApplicationTerm term)
			throws TermException {
		if (term.getParameters().length != 2) {
			throw new TermIsNotAffineException(
					"Unsupported number of parameters", term);
		}
		String fname = term.getFunction().getName();
		LinearInequality li1 =
				LinearInequality.fromTerm(term.getParameters()[0]);
		LinearInequality li2 =
				LinearInequality.fromTerm(term.getParameters()[1]);
		LinearInequality res;
		if (fname.equals(">=")) {
			li2.mult(Rational.MONE);
			res = li1;
			res.add(li2);
			res.setStrict(false);
		} else if (fname.equals("<=")) {
			li1.mult(Rational.MONE);
			res = li1;
			res.add(li2);
			res.setStrict(false);
		} else if (fname.equals(">")) {
			li2.mult(Rational.MONE);
			res = li1;
			res.add(li2);
			res.setStrict(true);
		} else if (fname.equals("<")) {
			res = li1;
			res.mult(Rational.MONE);
			res.add(li2);
			res.setStrict(true);
		} else {
			throw new TermIsNotAffineException("Expected an inequality.", term);
		}
		return res;
	}
	
	/**
	 * Convert a term into a polyhedron
	 * @param term the input term
	 * @return the polyhedron described by term
	 * @throws TermException if term is not a conjunction of linear inequalities
	 */
	public static List<LinearInequality> convert(Term term)
			throws TermException {
		List<LinearInequality> terms = new ArrayList<LinearInequality>();
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appt = (ApplicationTerm) term;
			String fname = appt.getFunction().getName();
			if (fname.equals("and")) {
				for (Term t : appt.getParameters()) {
					terms.addAll(convert(t));
				}
			} else if (fname.equals("true")) {
				// Add trivial linear inequality 0 ≤ 0.
				LinearInequality li = new LinearInequality();
				terms.add(li);
			} else if (fname.equals("="))  {
				Term param0 = appt.getParameters()[0];
				Sort param0sort = param0.getSort();
				if (param0sort.isNumericSort()) {
					terms.add(convertAtom(appt));
				} else if (param0sort.getName().equals("Bool")) {
					throw new TermException("Term is not in DNF", term);
				} else {
					throw new TermException("Unknown sort in equality", term);
				}
			} else if (fname.equals("<") || fname.equals(">")
					|| fname.equals("<=") || fname.equals(">=")) {
				terms.add(convertAtom(appt));
			} else {
				throw new UnknownFunctionException(appt);
			}
		} else if (term instanceof TermVariable)
			throw new TermException("Term is not in DNF", term);
		else {
			throw new TermException("Expected application term.", term);
		}
		return terms;
	}
}
