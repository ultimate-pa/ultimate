/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IOutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation.ISuccessorProvider;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

/**
 * Compute SCCs of an automaton. Allows to restrict computation to a subgraph (subset of states with corresponding
 * edges) of the automaton. This computation should work for each {@link IRabinAutomaton}, however, it is only sound if
 * each return transition is reachable (i.e., each transition can actually be taken).
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class AutomatonSccComputation<LETTER, STATE> {

	private final Collection<StronglyConnectedComponent<STATE>> mBalls;

	/**
	 * Computes accepting SCCs of an automaton.
	 *
	 * @param services
	 *            Ultimate services
	 * @param automaton
	 *            Rabin automaton
	 */
	public AutomatonSccComputation(final AutomataLibraryServices services,
			final IRabinAutomaton<LETTER, STATE> automaton) {
		final Set<STATE> init = new HashSet<>();
		automaton.getInitialStates().forEach(init::add);

		final RabinSccComputation<STATE> sccComputation =
				new RabinSccComputation<>(services.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID),
						new RabinSuccessorProvider(automaton), automaton.size(), init);

		mBalls = sccComputation.getBalls();
	}

	/**
	 * Returns all balls of the computed SCC.
	 *
	 * @return balls
	 */
	public Collection<StronglyConnectedComponent<STATE>> getBalls() {
		return mBalls;
	}

	/**
	 * Returns the first ball of the computed SCC.
	 *
	 * @return ball
	 */
	public Set<STATE> getExampleBall() {
		return getBalls().iterator().next().getNodes();
	}

	/**
	 * Provides - for a given state - all states that are
	 * <ul>
	 * <li>successors of internal transitions and
	 * <li>contained in the initial state set.
	 * </ul>
	 *
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
	 */
	private class RabinSuccessorProvider implements ISuccessorProvider<STATE> {

		private final IRabinAutomaton<LETTER, STATE> mAutomaton;

		public RabinSuccessorProvider(final IRabinAutomaton<LETTER, STATE> automaton) {
			mAutomaton = automaton;
		}

		private <E extends IOutgoingTransitionlet<LETTER, STATE>> Iterator<STATE>
				getStateContainerIterator(final Iterator<E> iterator) {
			return new Iterator<>() {

				@Override
				public boolean hasNext() {
					return iterator.hasNext();
				}

				@Override
				public STATE next() {
					return iterator.next().getSucc();
				}
			};
		}

		@Override
		public Iterator<STATE> getSuccessors(final STATE state) {
			return getStateContainerIterator(mAutomaton.getSuccessors(state).iterator());
		}
	}
}
