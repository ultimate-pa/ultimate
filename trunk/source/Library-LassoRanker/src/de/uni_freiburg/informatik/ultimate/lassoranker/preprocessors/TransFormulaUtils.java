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
package de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Some static methods for TransFormulaLR 
 * 
 * @author Matthias Heizmann
 */
public class TransFormulaUtils {



	public static boolean allVariablesAreInVars(List<Term> terms, TransFormulaLR tf) {
		for (Term term : terms) {
			if (!allVariablesAreInVars(term, tf)) {
				return false;
			}
		}
		return true;
	}

	public static boolean allVariablesAreOutVars(List<Term> terms, TransFormulaLR tf) {
		for (Term term : terms) {
			if (!allVariablesAreOutVars(term, tf)) {
				return false;
			}
		}
		return true;
	}

	public static boolean allVariablesAreInVars(Term term, TransFormulaLR tf) {
		for (TermVariable tv : term.getFreeVars()) {
			if (!isInvar(tv, tf)) {
				return false;
			}
		}
		return true;
	}

	public static boolean allVariablesAreOutVars(Term term, TransFormulaLR tf) {
		for (TermVariable tv : term.getFreeVars()) {
			if (!isOutvar(tv, tf)) {
				return false;
			}
		}
		return true;
	}

	public static boolean isInvar(TermVariable tv, TransFormulaLR tf) {
		return tf.getInVarsReverseMapping().keySet().contains(tv);
	}

	public static boolean isOutvar(TermVariable tv, TransFormulaLR tf) {
		return tf.getOutVarsReverseMapping().keySet().contains(tv);
	}




}