/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.CoveringOptimizationVisitor.ICoveringRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * A covering relation for product automata (union, intersection or difference).
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <S1>
 *            The state type of the product's left operand
 * @param <S2>
 *            The state type of the product's right operand
 * @param <S>
 *            The state type of the product automaton
 */
public class ProductCoveringRelation<S1, S2, S> implements ICoveringRelation<S> {
	private final Function<S, S1> mGetLeftState;
	private final ICoveringRelation<S1> mLeftOperand;

	private final Function<S, S2> mGetRightState;
	private final ICoveringRelation<S2> mRightOperand;

	public ProductCoveringRelation(final Function<S, S1> getLeft, final ICoveringRelation<S1> leftOperand,
			final Function<S, S2> getRight, final ICoveringRelation<S2> rightOperand) {
		mGetLeftState = getLeft;
		mLeftOperand = leftOperand;
		mGetRightState = getRight;
		mRightOperand = rightOperand;
	}

	@Override
	public boolean covers(final S oldState, final S newState) {
		return mLeftOperand.covers(mGetLeftState.apply(oldState), mGetLeftState.apply(newState))
				&& mRightOperand.covers(mGetRightState.apply(oldState), mGetRightState.apply(newState));
	}

	@Override
	public Object getKey(final S state) {
		final Object left = mLeftOperand.getKey(mGetLeftState.apply(state));
		final Object right = mRightOperand.getKey(mGetRightState.apply(state));
		if (left == null) {
			return right;
		}
		if (right == null) {
			return left;
		}
		return new Pair<>(left, right);
	}
}
