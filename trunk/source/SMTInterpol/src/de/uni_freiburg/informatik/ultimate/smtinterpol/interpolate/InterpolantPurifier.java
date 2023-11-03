/*
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.Occurrence;

/**
 * Purify a interpolant, i.e., replace every occurrence of a non-shared term by
 * an auxiliary variable and add the corresponding auxiliary variables to the
 * map.
 *
 * @author Jochen Hoenicke, based on code from Elisabeth Henkel
 *
 */
public class InterpolantPurifier extends TermTransformer {
	private final Interpolator mInterpolator;
	private int mPartition;

	public InterpolantPurifier(Interpolator interpolator) {
		mInterpolator = interpolator;
	}

	@Override
	public void convert(final Term oldTerm) {
		if (oldTerm instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) oldTerm;
			final FunctionSymbol funcSym = appTerm.getFunction();
			final Occurrence funcOccurrence = mInterpolator.getOccurrence(funcSym);
			if (!funcOccurrence.isAB(mPartition)) {
				// we need to replace this local function by a purification variable
				final TermVariable auxVar = mInterpolator.getOrCreatePurificationVariable(oldTerm);
				setResult(auxVar);
				return;
			}
		}
		super.convert(oldTerm);
	}

	/**
	 * Purify a term so that it only contains shared symbols for the given
	 * partition. Every non-shared sub-term is replaced by the corresponding
	 * purification variable.
	 *
	 * @param interpolant the term to purify.
	 * @param partition   the partition, which is used to determine if a symbol is
	 *                    shared.
	 * @return the purified term.
	 */
	public Term purify(Term interpolant, int partition) {
		mPartition = partition;
		return transform(interpolant);
	}
}
