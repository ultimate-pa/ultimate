/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword;

import java.util.Set;
import java.util.function.Consumer;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates.DoubleDeckerReachability;

/**
 * Extension of {@link NestedWordAutomatonFilteredStates} for double deckers.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class DoubleDeckerAutomatonFilteredStates<LETTER, STATE> extends NestedWordAutomatonFilteredStates<LETTER, STATE>
		implements IDoubleDeckerAutomaton<LETTER, STATE> {
	/**
	 * Extended constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param automaton
	 *            automaton
	 * @param remainingStates
	 *            remaining states
	 * @param newInitials
	 *            new initial states
	 * @param newFinals
	 *            new final states
	 * @throws AutomataOperationCanceledException
	 *             if timeout exceeds
	 */
	public DoubleDeckerAutomatonFilteredStates(final AutomataLibraryServices services,
			final NestedWordAutomatonReachableStates<LETTER, STATE> automaton, final Set<STATE> remainingStates,
			final Set<STATE> newInitials, final Set<STATE> newFinals) throws AutomataOperationCanceledException {
		super(services, automaton, remainingStates, newInitials, newFinals);
//		assert (successorOfRemovedStatesAreRemoved());
		assert (new DownStateConsistencyCheck<>(services, this)).getResult() : "down states inconsistent";
	}

	/**
	 * Short constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param automaton
	 *            automaton
	 * @param ancestorComputation
	 *            ancestor computation object
	 * @throws AutomataOperationCanceledException
	 *             if timeout exceeds
	 */
	public DoubleDeckerAutomatonFilteredStates(final AutomataLibraryServices services,
			final NestedWordAutomatonReachableStates<LETTER, STATE> automaton,
			final NestedWordAutomatonReachableStates<LETTER, STATE>.AncestorComputation ancestorComputation)
			throws AutomataOperationCanceledException {
		super(services, automaton, ancestorComputation);
//		assert (successorOfRemovedStatesAreRemoved());
		assert (new DownStateConsistencyCheck<>(mServices, this)).getResult() : "down states inconsistent";
	}

	private boolean successorOfRemovedStatesAreRemoved() {
		final WasStateRemovedChecker f = new WasStateRemovedChecker();
		for (final STATE s : super.mNwa.getStates()) {
			if (!mRemainingStates.contains(s)) {
				NestedWordAutomataUtils.applyToReachableSuccessors(mNwa, s, f);
			}
		}
		return f.doesPropertyHold();
	}

	/**
	 * {@inheritDoc}
	 *
	 * @deprecated Use the {@link #isDoubleDecker(Object, Object)} check instead.
	 */
	@Override
	@Deprecated
	public Set<STATE> getDownStates(final STATE upState) {
		if (mAncestorComputation != null) {
			return mAncestorComputation.getDownStates(upState,
					DoubleDeckerReachability.REACHABLE_AFTER_REMOVAL_OF_PRECIOUS_NOT_REACHERS);
		}
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean isDoubleDecker(final STATE upState, final STATE downState) {
		return mAncestorComputation.isDownState(upState, downState,
				DoubleDeckerReachability.REACHABLE_AFTER_REMOVAL_OF_PRECIOUS_NOT_REACHERS);
	}

	/**
	 * Checks whether a state was removed.
	 *
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	private class WasStateRemovedChecker implements Consumer<STATE> {
		private boolean mPropertyHolds;

		/**
		 * Constructor.
		 */
		public WasStateRemovedChecker() {
			this.mPropertyHolds = true;
		}

		@Override
		public void accept(final STATE state) {
			final boolean wasRemoved = !mRemainingStates.contains(state);
			assert wasRemoved : "state " + state + " was not removed but some predecessor was";
			mPropertyHolds &= wasRemoved;
		}

		/**
		 * @return {@code true} iff property holds.
		 */
		public boolean doesPropertyHold() {
			return mPropertyHolds;
		}
	}
}
