/*
 * Copyright (C) 2023 Philipp Müller (pm251@venus.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Computes the acceptance of an infinite word for a Rabin automaton
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 *            letter
 * @param <STATE>
 *            state
 * @param <CRSF>
 *            crsf
 */
public class Accepts<LETTER, STATE, CRSF extends IStateFactory<STATE>> extends GeneralOperation<LETTER, STATE, CRSF> {
	private final boolean mResult;

	/**
	 * Checks acceptance of a NestedLassoWord on IRabinAutomaton
	 *
	 * @param services
	 *            services
	 * @param automaton
	 *            The Rabin automaton which is simulated for acceptance purposes
	 * @param word
	 *            The word that is evaluated on automaton
	 * @throws AutomataOperationCanceledException
	 *             exception if isCancellationRequested
	 */
	public Accepts(final AutomataLibraryServices services, final IRabinAutomaton<LETTER, STATE> automaton,
			final NestedLassoWord<LETTER> word) throws AutomataOperationCanceledException {
		super(services);
		// TODO: Could we use another type of lasso-words here instead?
		if (!word.getStem().hasEmptyNestingRelation() || !word.getLoop().hasEmptyNestingRelation()) {
			throw new AssertionError("Rabin automata cannot handle calls/returns.");
		}
		mResult = computeResult(automaton, word.getStem().asList(), word.getLoop().asList());
	}

	/**
	 * Checks acceptance of a Word split into stem and loop on IRabinAutomaton
	 *
	 * @param services
	 *            services
	 * @param automaton
	 *            The Rabin automaton which is simulated for acceptance purposes
	 * @param stem
	 *            The stem of the word that is evaluated on automaton
	 * @param loop
	 *            The loop of the word that is evaluated on automaton
	 * @throws AutomataOperationCanceledException
	 *             exception if isCancellationRequested
	 */
	public Accepts(final AutomataLibraryServices services, final IRabinAutomaton<LETTER, STATE> automaton,
			final List<LETTER> stem, final List<LETTER> loop) throws AutomataOperationCanceledException {
		super(services);
		mResult = computeResult(automaton, stem, loop);
	}

	/*
	 * computes paths to accepting states with iterative letter evaluation and returns true iff if one of them has a
	 * valid infinite loop returns false if no new situations with letter state pairs are found iff no true value was
	 * returned first
	 */
	private boolean computeResult(final IRabinAutomaton<LETTER, STATE> automaton, final List<LETTER> stem,
			final List<LETTER> loop) throws AutomataOperationCanceledException {
		// computes all states which the automaton can be in after the stem is consumed
		final ArrayList<STATE> currentStateSet = stemEvaluation(automaton, stem);
		// a index referencing the current letter/position in loop which is to be consumed in this step
		int loopIndex = 0;
		// situations refer to the combination of a state and a letter to be consumed(referenced by loopIndex), if one
		// situation is encountered twice it is not to be evaluated again since its effects/successors are already
		// considered
		final HashSet<Pair<Integer, STATE>> uniqueSituations = new HashSet<>();
		final HashSet<Pair<Integer, STATE>> visitedSituations = new HashSet<>();
		currentStateSet.forEach(x -> uniqueSituations.add(new Pair<>(0, x)));
		do {
			if (isCancellationRequested()) {
				throw new AutomataOperationCanceledException(getClass());
			}
			// if there are no transitions for an input letter the automaton does not accept
			if (currentStateSet.isEmpty()) {
				return false;
			}
			final ArrayList<STATE> temp = new ArrayList<>();
			for (final STATE state : currentStateSet) {
				// if there is a loop on a accepting, nonFinite state the automaton accepts, since visited situations
				// already encountered the test for hasLoop we don't have to test them again
				if (automaton.isAccepting(state) && !automaton.isFinite(state)
						&& !visitedSituations.contains(new Pair<>(loopIndex, state))
						&& hasLoop(automaton, state, loop, loopIndex)) {
					return true;
				}
				visitedSituations.add(new Pair<>(loopIndex, state));
				for (final OutgoingInternalTransition<LETTER, STATE> possibleTransition : automaton.getSuccessors(state,
						loop.get(loopIndex))) {
					final STATE sucessor = possibleTransition.getSucc();
					if (!visitedSituations.contains(new Pair<>((loopIndex + 1) % loop.size(), sucessor))) {
						temp.add(sucessor);
					}
				}
			}
			currentStateSet.clear();
			currentStateSet.addAll(temp);
			// for the next step we consider the next letter, if we consumed loop once the next letter will therefore be
			// the one at index 0 of loop, so it can be consumed "infinitely" often
			loopIndex = (loopIndex + 1) % loop.size();
			for (final STATE state : currentStateSet) {
				uniqueSituations.add(new Pair<>(loopIndex, state));
			}
		} while (!uniqueSituations.equals(visitedSituations));
		// if there are only non-accepting self loops(no new situations are produced) the automaton does not accept
		return false;
	}

	/**
	 * Produces a new set of starting states that is valid after stem is read. Works similar to a NFA interpreter.
	 */
	private ArrayList<STATE> stemEvaluation(final IRabinAutomaton<LETTER, STATE> automaton, final List<LETTER> stem) {
		ArrayList<STATE> currentStateSet = new ArrayList<>(automaton.getInitialStates());
		// we consume each letter from the stem in a step and derive from it a new situation with a respective stateSet
		for (final LETTER letter : stem) {
			if (currentStateSet.isEmpty()) {
				break;
			}
			final ArrayList<STATE> temp = new ArrayList<>();
			for (final STATE currentState : currentStateSet) {
				for (final OutgoingInternalTransition<LETTER, STATE> possibleTransition : automaton
						.getSuccessors(currentState, letter)) {
					temp.add(possibleTransition.getSucc());
				}
			}
			currentStateSet = temp;
		}
		return currentStateSet;
	}

	/**
	 * Tests if a loop exists from state to itself with input loop
	 */
	private boolean hasLoop(final IRabinAutomaton<LETTER, STATE> automaton, final STATE start, final List<LETTER> loop,
			final int loopIndex) throws AutomataOperationCanceledException {
		ArrayList<STATE> currentStateSet = new ArrayList<>();

		int localLoopIndex = loopIndex;
		final HashSet<Pair<Integer, STATE>> uniqueSituations = new HashSet<>();
		final HashSet<Pair<Integer, STATE>> visitedSituations = new HashSet<>();

		currentStateSet.add(start);
		uniqueSituations.add(new Pair<>(loopIndex, start));
		do {
			if (isCancellationRequested()) {
				throw new AutomataOperationCanceledException(getClass());
			}
			if (currentStateSet.isEmpty()) {
				return false;
			}
			final ArrayList<STATE> temp = new ArrayList<>();
			for (final STATE state : currentStateSet) {
				for (final OutgoingInternalTransition<LETTER, STATE> possibleTransition : automaton.getSuccessors(state,
						loop.get(localLoopIndex))) {
					final STATE sucessor = possibleTransition.getSucc();
					// we only consider nonFinite states in the loop evaluation, all finite properties are taken care of
					// by other methods
					if (!automaton.isFinite(sucessor)) {
						// if we reach a situation where a nonzero multiple of loop has been consumed and reach the
						// original state we found a loop
						if (loopIndex == (localLoopIndex + 1) % loop.size() && sucessor.equals(start)) {
							return true;
						}
						if (!visitedSituations.contains(new Pair<>((localLoopIndex + 1) % loop.size(), sucessor))) {
							temp.add(sucessor);
						}
					}
				}
				visitedSituations.add(new Pair<>(localLoopIndex, state));
			}
			currentStateSet = temp;
			// for the next step we consider the next letter, if we consumed loop once the next letter will therefore be
			// the one at index 0 of loop, so it can be consumed "infinitely" often
			localLoopIndex = (localLoopIndex + 1) % loop.size();
			for (final STATE state : currentStateSet) {
				uniqueSituations.add(new Pair<>(localLoopIndex, state));
			}
		} while (!uniqueSituations.equals(visitedSituations));
		// if there are only self loops for other states(no new situations are produced) the automaton has no loop at
		// start
		return false;
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}
}
