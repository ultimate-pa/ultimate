/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.variables;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermIsNotAffineException;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.UnknownFunctionException;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Generate a list of LinearInequality instances from a formula in disjunctive normal form
 *
 * @author Jan Leike
 * @author Matthias Heizmann
 */
public class InequalityConverter {

	/**
	 * Defines what the {@link InequalityConverter} does while processing a (Sub-) Term that is nonlinear.
	 */
	public enum NlaHandling {
		/**
		 * Replace nonlinear (sub)term by true.
		 */
		OVERAPPROXIMATE,
		/**
		 * Replace nonlinear (sub)term by false.
		 */
		UNDERAPPROXIMATE,
		/**
		 * Throw exception if (sub)term is nonlinear.
		 */
		EXCEPTION
	}

	/**
	 * Convert an atomary term that is an (in-)equality into an instance of LinearInequality
	 *
	 * @param term
	 *            atomary term
	 * @returns the linear inequality
	 * @throws TermException
	 *             if the input term cannot be reduced to a LinearInequality
	 */
	private static LinearInequality convertAtom(final ApplicationTerm term) throws TermException {
		if (term.getParameters().length != 2) {
			throw new TermIsNotAffineException("Unsupported number of parameters", term);
		}
		final String fname = term.getFunction().getName();
		LinearInequality li1;
		LinearInequality li2;
		try {
			li1 = LinearInequality.fromTerm(term.getParameters()[0]);
			li2 = LinearInequality.fromTerm(term.getParameters()[1]);
		} catch (final TermIsNotAffineException tinae) {
			throw tinae;
		}

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
	 *
	 * @param term
	 *            the input term
	 * @return the polyhedron described by term
	 * @throws TermException
	 *             if term is not a conjunction of linear inequalities
	 */
	public static List<LinearInequality> convert(final Term term, final NlaHandling nlaHandling) throws TermException {
		final List<LinearInequality> terms = new ArrayList<>();
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appt = (ApplicationTerm) term;
			final String fname = appt.getFunction().getName();
			if (fname.equals("and")) {
				for (final Term t : appt.getParameters()) {
					terms.addAll(convert(t, nlaHandling));
				}
			} else if (fname.equals("true")) {
				// Add trivial linear inequality 0 ≤ 0.
				final LinearInequality li = new LinearInequality();
				terms.add(li);
			} else if (fname.equals("=")) {
				final Term param0 = appt.getParameters()[0];
				final Sort param0sort = param0.getSort();
				if (param0sort.isNumericSort()) {
					final LinearInequality converted = tryToConvertAtom(nlaHandling, appt);
					terms.add(converted);
				} else if (SmtSortUtils.isBoolSort(param0sort)) {
					throw new TermException(TermException.IS_NOT_IN_DNF, term);
				} else {
					throw new TermException(TermException.UNKNOWN_SORT_IN_EQUALITY, term);
				}
			} else if (fname.equals("<") || fname.equals(">") || fname.equals("<=") || fname.equals(">=")) {
				final LinearInequality converted = tryToConvertAtom(nlaHandling, appt);
				terms.add(converted);
			} else {
				throw new UnknownFunctionException(appt);
			}
		} else if (term instanceof TermVariable) {
			throw new TermException(TermException.IS_NOT_IN_DNF, term);
		} else {
			throw new TermException(TermException.EXPECTED_APPLICATION_TERM, term);
		}
		return terms;
	}

	private static LinearInequality tryToConvertAtom(final NlaHandling nlaHandling, final ApplicationTerm appt)
			throws TermException, TermIsNotAffineException {
		LinearInequality converted;
		try {
			converted = convertAtom(appt);
		} catch (final TermIsNotAffineException tinae) {
			if (tinae.getMessage().equals(TermIsNotAffineException.s_MultipleNonConstantFactors)) {
				switch (nlaHandling) {
				case EXCEPTION: {
					throw tinae;
				}
				case OVERAPPROXIMATE: {
					converted = new LinearInequality();
					break;
				}
				case UNDERAPPROXIMATE: {
					converted = LinearInequality.constructFalse();
					break;
				}
				default:
					throw new AssertionError("unknown case");
				}

			} else {
				throw tinae;
			}
		}
		return converted;
	}
}
