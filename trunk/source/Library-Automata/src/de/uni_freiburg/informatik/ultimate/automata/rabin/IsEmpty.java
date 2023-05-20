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
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IOutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.TransformIterator;
import de.uni_freiburg.informatik.ultimate.util.scc.DefaultSccComputation;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

/**
 * A class to check emptiness of IRabinAutomaton
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 * @param <CRSF>
 *            crsf type
 */
public class IsEmpty<LETTER, STATE, CRSF extends IStateFactory<STATE>> extends GeneralOperation<LETTER, STATE, CRSF> {
	private final Boolean mResult;
	private final IRabinAutomaton<LETTER, STATE> mAutomaton;
	private final Set<STATE> mEvidence;

	/**
	 * Computes the emptiness of automaton and holds information about the emptiness
	 *
	 * @param services
	 *            services
	 * @param automaton
	 *            automaton
	 */
	public IsEmpty(final AutomataLibraryServices services, final IRabinAutomaton<LETTER, STATE> automaton) {
		super(services);
		// Reduces the automaton to its traversable core
		// cuts off non reachable final states
		mAutomaton = automaton;
		final IRabinAutomaton<LETTER, STATE> suffixAutomaton = getSuffixAutomaton(mAutomaton);

		final Set<STATE> init = suffixAutomaton.getInitialStates();

		final DefaultSccComputation<STATE> sccComputation =
				new DefaultSccComputation<>(services.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID),
						x -> new TransformIterator<>(suffixAutomaton.getSuccessors(x).iterator(),
								IOutgoingTransitionlet::getSucc),
						suffixAutomaton.size(), init);
		mEvidence = getEvidence(init, sccComputation.getBalls());
		mResult = mEvidence.isEmpty();
	}

	private Set<STATE> getEvidence(final Set<STATE> init, final Collection<StronglyConnectedComponent<STATE>> balls) {
		for (final StronglyConnectedComponent<STATE> ball : balls) {
			for (final STATE node : init) {
				if (ball.getNodes().contains(node)) {
					return ball.getNodes();
				}
			}
		}
		return Set.of();
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}

	public NestedLassoWord<LETTER> getCounterexample() throws AutomataOperationCanceledException {
		if (mEvidence.isEmpty()) {
			return null;
		}
		// get one random accepting State from evidence
		final STATE hondaState = mEvidence.stream().filter(mAutomaton::isAccepting).findAny().get();
		return new NestedLassoWord<>(getStem(hondaState), getLoop(hondaState));
	}

	private NestedWord<LETTER> getStem(final STATE hondaState) throws AutomataOperationCanceledException {
		final HashSet<STATE> exploredStates = new HashSet<>();
		return computeWord(mAutomaton.getInitialStates(), hondaState, exploredStates::add);
	}

	private NestedWord<LETTER> getLoop(final STATE hondaState) throws AutomataOperationCanceledException {
		final HashSet<STATE> missingStates = new HashSet<>(mEvidence);
		return computeWord(Set.of(hondaState), hondaState, missingStates::remove);
	}

	@SuppressWarnings("unchecked")
	private NestedWord<LETTER> computeWord(final Set<STATE> initialStates, final STATE goalState,
			final Predicate<STATE> statePredicate) throws AutomataOperationCanceledException {
		HashRelation<List<LETTER>, STATE> wordStateMap = new HashRelation<>();
		wordStateMap.addAllPairs(List.of(), initialStates);

		while (!isCancellationRequested()) {
			final HashRelation<List<LETTER>, STATE> temp = new HashRelation<>();
			for (final Entry<List<LETTER>, HashSet<STATE>> word : wordStateMap.entrySet()) {
				for (final STATE state : word.getValue()) {
					for (final OutgoingInternalTransition<LETTER, STATE> transition : mAutomaton.getSuccessors(state)) {
						final STATE succ = transition.getSucc();
						if (statePredicate.test(succ)) {
							final ArrayList<LETTER> newWord = new ArrayList<>(word.getKey());
							newWord.add(transition.getLetter());
							if (succ.equals(goalState)) {
								return NestedWord.nestedWord(new Word<>((LETTER[]) (newWord.toArray())));
							}
							temp.addPair(newWord, succ);
						}
					}
				}
			}
			wordStateMap = temp;
		}
		throw new AutomataOperationCanceledException(getClass());
	}

	/**
	 * @param automaton
	 *            a fully traversable Rabin automaton
	 *
	 *            Generates a automaton that starts from the Honda/accepting states of this automaton and removes all
	 *            finite states
	 */
	private RabinAutomaton<LETTER, STATE> getSuffixAutomaton(final IRabinAutomaton<LETTER, STATE> automaton) {
		final RabinAutomaton<LETTER, STATE> reachable = RabinAutomataUtils.computeReachableStates(automaton);
		final RabinAutomaton<LETTER, STATE> nonReducedAutomaton =
				new RabinAutomaton<>(reachable.getAlphabet(), reachable.getStates(), reachable.getAcceptingStates(),
						reachable.getAcceptingStates(), reachable.getFiniteStates(), reachable.getTransitions());
		return RabinAutomataUtils.computeReachableIgnoredStates(nonReducedAutomaton, reachable.getFiniteStates());
	}

	@Override
	public boolean checkResult(final CRSF stateFactory) throws AutomataOperationCanceledException {
		boolean result = true;
		if (Boolean.FALSE.equals(mResult)) {
			final NestedLassoWord<LETTER> counterExample = getCounterexample();
			result = new Accepts<>(mServices, mAutomaton, counterExample).getResult();
		}
		return result;
	}
}
