/*
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;

/**
 * Info class for quantified terms. This class contains helper methods to classify quantified terms.
 * 
 * @author Tanja Schindler
 */
public class QuantifiedTermInfo {

	private QuantifiedTermInfo() {
		// Not meant to be instantiated
	}

	/**
	 * Check if a given term is essentially uninterpreted, i.e., it is ground or variables only appear as arguments of
	 * uninterpreted functions.
	 * 
	 * TODO Nonrecursive.
	 * 
	 * @param term
	 *            The term to check.
	 * @return true if the term is essentially uninterpreted, false otherwise.
	 */
	public static boolean isEssentiallyUninterpreted(final Term term) {
		if (term.getFreeVars().length == 0) {
			return true;
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final FunctionSymbol func = appTerm.getFunction();
			if (!func.isInterpreted()) {
				for (Term arg : appTerm.getParameters()) {
					if (!(arg instanceof TermVariable)) {
						if (!isEssentiallyUninterpreted(arg)) {
							return false;
						}
					}
				}
				return true;
			} else if (func.getName() == "select") {
				final Term[] params = appTerm.getParameters();
				if (params[0] instanceof TermVariable || !isEssentiallyUninterpreted(params[0])) {
					return false; // Quantified arrays are not allowed.
				}
				if (!(params[1] instanceof TermVariable) && !isEssentiallyUninterpreted(params[1])) {
					return false;
				}
				return true;
			} else if (func.getName() == "+" || func.getName() == "-" || func.getName() == "*") {
				final SMTAffineTerm affineTerm = SMTAffineTerm.create(term);
				for (Term summand : affineTerm.getSummands().keySet()) {
					if (!isEssentiallyUninterpreted(summand)) {
						return false;
					}
				}
				return true;
			} else {
				return false;
			}
		} else {
			return false;
		}
	}

	/**
	 * Check if all summands of an affine term are "simple" EU terms, i.e., they are ground, or an application of an
	 * uninterpreted function where all arguments are variables or simple EU terms. (Exception: select behaves as an
	 * uninterpreted function but may not have a variable as first argument.)
	 * 
	 * @param affine
	 *            the SMTAffineTerm to check.
	 * @return true, if all summands are "simple" EU terms; false otherwise.
	 */
	public static boolean hasOnlySimpleEssentiallyUninterpretedSummands(final SMTAffineTerm affine) {
		boolean isAllSimple = true;
		for (final Term smd : affine.getSummands().keySet()) {
			isAllSimple &= isSimpleEssentiallyUninterpreted(smd);
		}
		return isAllSimple;
	}

	/**
	 * Check if a term is a "simple" EU term, i.e., it is ground, or an application of an uninterpreted function where
	 * all arguments are variables or simple EU terms. (Exception: select behaves as an uninterpreted function but may
	 * not have a variable as first argument.)
	 * 
	 * TODO Nonrecursive.
	 * 
	 * @param term
	 *            the term to check.
	 * @return true, if the term is a "simple" EU term, false otherwise.
	 */
	public static boolean isSimpleEssentiallyUninterpreted(final Term term) {
		if (term.getFreeVars().length != 0) {
			if (term instanceof TermVariable) {
				return false;
			} else {
				assert term instanceof ApplicationTerm;
				final ApplicationTerm at = (ApplicationTerm) term;
				final FunctionSymbol func = at.getFunction();
				if (func.isInterpreted() && !func.getName().equals("select")) {
					return false;
				}
				final Term[] args = at.getParameters();
				if (func.getName().equals("select")) {
					if (!isSimpleEssentiallyUninterpreted(args[0])) {
						return false; // Quantified arrays are not allowed.
					}
					if (!(args[1] instanceof TermVariable) && !isSimpleEssentiallyUninterpreted(args[1])) {
						return false;
					}
				} else {
					for (final Term arg : args) {
						if (!(arg instanceof TermVariable) && !isSimpleEssentiallyUninterpreted(arg)) {
							return false;
						}
					}
				}
			}
		}
		return true;
	}
}
