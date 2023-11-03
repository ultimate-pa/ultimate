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
package de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors;

import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Interface for classes that store information about dead end states found during an automaton traversal.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <S>
 *            If R is some type of product state, and this product nature influences dead ends, then S is the type of
 *            underlying state (see {@link #copyDeadEndInformation(S, S)} for details. If R is not a type of product
 *            states, use the same type as R.
 * @param <R>
 *            Type of states about which dead end information is stored
 */
public interface IDeadEndStore<S, R> {
	/**
	 * Determines if a state has been marked as dead end (see {@link #addDeadEndState(R)}).
	 *
	 * @param state
	 *            the state which might be a dead end
	 * @return true if the state has already been marked as dead end, false otherwise
	 */
	boolean isDeadEndState(final R state);

	/**
	 * Marks a state as dead end.
	 *
	 * @param state
	 *            the dead end state
	 */
	void addDeadEndState(final R state);

	/**
	 * Copies dead end information from a given state to another.
	 *
	 * If R is not a product state type, this simply means that if the first state is known to be a dead end, we also
	 * mark the new state as dead end.
	 *
	 * If R is a type of product state, this means that for any combination of the first state with other product
	 * components X that is known to be a dead end, we also mark the combination of the new state and the same extra
	 * information X as dead end.
	 *
	 * @param originalState
	 *            The state whose dead end information should be copied.
	 * @param newState
	 *            The state for which dead end information is added
	 */
	void copyDeadEndInformation(final S originalState, final S newState);

	/**
	 * A simple dead end store for non-product states.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <S>
	 *            The type of states
	 */
	final class SimpleDeadEndStore<S> implements IDeadEndStore<S, S> {
		private final Set<S> mDeadEndSet = new HashSet<>();

		@Override
		public boolean isDeadEndState(final S state) {
			return mDeadEndSet.contains(state);
		}

		@Override
		public void addDeadEndState(final S state) {
			mDeadEndSet.add(state);

		}

		@Override
		public void copyDeadEndInformation(final S originalState, final S newState) {
			if (isDeadEndState(originalState)) {
				addDeadEndState(newState);
			}
		}
	}

	/**
	 * A dead end store for product states.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <S>
	 *            The underlying type of states for which dead end information can be transferred, see
	 *            {@link #copyDeadEndInformation(S, S)}.
	 * @param <R>
	 *            The type of states for which dead end information is stored
	 */
	final class ProductDeadEndStore<S, R> implements IDeadEndStore<S, R> {
		private final Function<R, S> mState2Original;
		private final Function<R, ?> mState2ExtraInfo;
		private final HashRelation<S, Object> mDeadEndRelation = new HashRelation<>();

		/**
		 * Creates a new instance.
		 *
		 * @param state2Original
		 *            Extracts the underlying state of type S from a product state of type R
		 * @param state2ExtraInfo
		 *            Extracts the remaining components of the product state
		 */
		public ProductDeadEndStore(final Function<R, S> state2Original, final Function<R, ?> state2ExtraInfo) {
			mState2Original = state2Original;
			mState2ExtraInfo = state2ExtraInfo;
		}

		@Override
		public boolean isDeadEndState(final R state) {
			return mDeadEndRelation.containsPair(mState2Original.apply(state), mState2ExtraInfo.apply(state));
		}

		@Override
		public void addDeadEndState(final R state) {
			mDeadEndRelation.addPair(mState2Original.apply(state), mState2ExtraInfo.apply(state));
		}

		@Override
		public void copyDeadEndInformation(final S originalState, final S newState) {
			mDeadEndRelation.addAllPairs(newState, mDeadEndRelation.getImage(originalState));
		}
	}
}
