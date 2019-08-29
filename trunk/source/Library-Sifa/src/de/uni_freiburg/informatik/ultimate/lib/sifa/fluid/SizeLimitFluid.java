/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.fluid;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;

public class SizeLimitFluid implements IFluid {

	private final int mMaxDagSize;
	private final int mMaxDisjuncts;

	/**
	 * Creates a new fluid.
	 * Negative values for limits disable the corresponding limit.
	 *
	 * @param maxDagSize Abstract when formula has dag size strictly greater than this
	 * @param maxDisjuncts Abstract when formula has strictly more disjuncts than this
	 */
	public SizeLimitFluid(final int maxDagSize, final int maxDisjuncts) {
		mMaxDagSize = maxDagSize;
		mMaxDisjuncts = maxDisjuncts;
	}

	@Override
	public boolean shallBeAbstracted(final IPredicate predicate) {
		final Term term = predicate.getFormula();
		return exceedsDagSizeLimit(term) || exceedsDisjunctLimit(term);
	}

	private boolean exceedsDagSizeLimit(final Term term) {
		if (mMaxDagSize < 0) {
			return false;
		}
		return new DAGSize().size(term) > mMaxDagSize;
	}

	private boolean exceedsDisjunctLimit(final Term term) {
		if (mMaxDisjuncts < 0) {
			return false;
		}
		return numberOfDisjuncts(term) > mMaxDisjuncts;
	}

	public static int numberOfDisjuncts(final Term term) {
		final boolean includeSubterms = true;
		return new ApplicationTermFinder("or", includeSubterms)
				.findMatchingSubterms(term).stream()
				.mapToInt(orTerm -> orTerm.getParameters().length)
				.sum();
	}

}
