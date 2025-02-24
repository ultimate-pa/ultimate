/*
 * Copyright (C) 2025 Veronika Klasen
 * Copyright (C) 2025 University of Freiburg
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

import java.util.HashMap;
import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IPersistentSetChoice;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;

/*
 * A visitor that constructs the Ample Set Reduction of the input automaton. Adaptation of the Automaton Construction Visitor.
 *
 * @param <L>
 *            The type of letters in the automaton
 * @param <S>
 *            The type of automaton states
 */

public class AmpleReductionConstructingVisitor<L, S> implements IDfsVisitor<L, S> {
	INwaOutgoingLetterAndTransitionProvider<L, S> mOriginalAutomaton;
	private final Predicate<S> mIsInitial;
	private final Predicate<S> mIsFinal;
	private final NestedWordAutomaton<L, S> mReductionAutomaton;
	private final IPersistentSetChoice<L, S> mPersistent;
	private final HashMap<S, Set<L>> mAmpleSets;

	public int mPruningCounter; // count the number of pruned transitions
	public int mNonTrivialCounter; // count the number of non-trivial ample sets
	public int mLoopCausedTrivial; // Originally non-trivial ample sets that became trivial bc of (A4: Cycle condition)

	/**
	 * Create a new visitor instance.
	 *
	 * @param operand
	 *            original automaton we want to reduce
	 * @param isInitial
	 *            Used to identify initial states in the constructed automaton
	 * @param isFinal
	 *            Used to identify final states in the constructed automaton
	 * @param alphabet
	 *            The alphabet of the constructed automaton
	 * @param services
	 *            Services used in the constructed automaton
	 * @param stateFactory
	 *            State factory used by the constructed automaton
	 * @param persistent
	 *            Used to compute the ample sets of states.
	 */
	public AmpleReductionConstructingVisitor(final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final Predicate<S> isInitial, final Predicate<S> isFinal, final VpAlphabet<L> alphabet,
			final AutomataLibraryServices services, final IEmptyStackStateFactory<S> stateFactory,
			final IPersistentSetChoice<L, S> persistent) {
		mOriginalAutomaton = operand;
		mIsInitial = isInitial;
		mIsFinal = isFinal;
		mPersistent = persistent;
		mReductionAutomaton = new NestedWordAutomaton<>(services, alphabet, stateFactory);
		// ! Trivial ample sets (ample set = set of all outgoing edges) are represented by null !
		mAmpleSets = new HashMap<>(); // store the ample sets of reduction states.
		// Get ample set of initial state. There should only be one initial state
		final S init = mOriginalAutomaton.getInitialStates().iterator().next();
		// persistent set is null for the trivial persistent set (which is the set of all outgoing edges)
		final Set<L> initAmple = mPersistent.persistentSet(init);
		if (!Objects.isNull(initAmple)) {
			mNonTrivialCounter++;
		}
		mAmpleSets.put(init, initAmple);
	}

	// Discover transitions (whose letters) are part of the ample set of the source state. Return 'false' to discover a
	// transition
	public boolean discoverTransition(final S source, final L letter, final S target, final boolean targetIsLoopNode) {
		// Cycle checking is outsourced to DepthFirstTraversal
		final Set<L> persistent = mAmpleSets.get(source);
		// Prune outgoing edges not in the state's ample set
		if (!Objects.isNull(persistent) && !persistent.contains(letter)) {
			mPruningCounter++;
			return true;
		}
		// Get the ample set of the new successor state
		Set<L> ample;
		// In case of loop closure, the ample set contains all outgoing edges
		if (targetIsLoopNode) {
			// Only added for curiosity/statistics.
			if (!Objects.isNull(mPersistent.persistentSet(target))) {
				mLoopCausedTrivial++;
			}
			ample = null;
		} else {
			ample = mPersistent.persistentSet(target);

		}
		if (!Objects.isNull(ample)) {
			mNonTrivialCounter++;
		}
		mAmpleSets.put(target, ample);

		if (!mReductionAutomaton.contains(target)) {
			assert mIsFinal.test(target) : "All states of the automaton should be final!";
			mReductionAutomaton.addState(mIsInitial.test(target), true, target);
		}
		// add transition from currentState to succState to the automaton
		mReductionAutomaton.addInternalTransition(source, letter, target);
		return false;
	}

	@Override
	// unchanged
	public boolean addStartState(final S state) {
		mReductionAutomaton.addState(true, mIsFinal.test(state), state);
		return false;
	}

	// unchanged
	public NestedWordAutomaton<L, S> getReductionAutomaton() {
		return mReductionAutomaton;
	}

}
