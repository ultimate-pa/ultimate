/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.partialorder.independence;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;

/**
 * Implements {@link ISymbolicIndependenceRelation} by explicitly checking independence and returning either the term
 * {@code true} or the term {@code false}.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters checked for independence
 */
public class ExplicitSymbolicIndependenceRelation<L, S> implements ISymbolicIndependenceRelation<L, S> {
	private final IIndependenceRelation<S, L> mUnderlying;
	private final S mTrueCondition;
	private final S mFalseCondition;

	public ExplicitSymbolicIndependenceRelation(final IIndependenceRelation<S, L> underlying, final S trueCondition,
			final S falseCondition) {
		mUnderlying = underlying;
		mTrueCondition = trueCondition;
		mFalseCondition = falseCondition;
	}

	@Override
	public S getCommutativityCondition(final S condition, final L a, final L b) {
		final var dependence = mUnderlying.isIndependent(condition, a, b);
		if (dependence == Dependence.INDEPENDENT) {
			return mTrueCondition;
		}
		return mFalseCondition;
	}

	@Override
	public boolean isSymmetric() {
		return mUnderlying.isSymmetric();
	}

	@Override
	public boolean isConditional() {
		return mUnderlying.isConditional();
	}
}
