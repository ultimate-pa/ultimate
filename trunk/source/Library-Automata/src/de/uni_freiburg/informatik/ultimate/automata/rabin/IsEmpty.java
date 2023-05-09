package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

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
import de.uni_freiburg.informatik.ultimate.util.scc.DefaultSccComputation;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation.ISuccessorProvider;
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
	private final RabinAutomaton<LETTER, STATE> mEagerAutomaton;
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
		mEagerAutomaton = RabinAutomataUtils.eagerAutomaton(automaton);

		final IRabinAutomaton<LETTER, STATE> suffixAutomaton = getSuffixAutomaton(mEagerAutomaton);

		final Set<STATE> init = new HashSet<>();
		suffixAutomaton.getInitialStates().forEach(init::add);

		final DefaultSccComputation<STATE> sccComputation =
				new DefaultSccComputation<>(services.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID),
						new RabinSuccessorProvider(suffixAutomaton), suffixAutomaton.size(), init);

		mEvidence = getEvidence(init, sccComputation.getBalls());
		mResult = mEvidence.isEmpty();
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}

	@SuppressWarnings("unchecked")
	public NestedLassoWord<LETTER> getCounterexample() throws AutomataOperationCanceledException {
		if (mEvidence.isEmpty()) {
			return null;
		}

		final Collection<STATE> possibleHondaStates = new ArrayList<>(mEvidence);
		possibleHondaStates.removeIf(x -> !mEagerAutomaton.isAccepting(x));
		final STATE hondaState = possibleHondaStates.iterator().next();

		return new NestedLassoWord<>(NestedWord.nestedWord(new Word<>((LETTER[]) getStem(hondaState).toArray())),
				NestedWord.nestedWord(new Word<>((LETTER[]) getLoop(hondaState).toArray())));
	}

	private List<LETTER> getLoop(final STATE hondaState) throws AutomataOperationCanceledException {

		// get one random accepting State from evidence
		final HashSet<STATE> initialSet = new HashSet<>();
		initialSet.add(hondaState);

		final HashSet<STATE> missingStates = new HashSet<>(mEvidence);

		HashMap<List<LETTER>, HashSet<STATE>> wordStateMap = new HashMap<>();
		wordStateMap.put(new ArrayList<>(), initialSet);

		while (!isCancellationRequested()) {

			final HashMap<List<LETTER>, HashSet<STATE>> temp = new HashMap<>();
			for (final Entry<List<LETTER>, HashSet<STATE>> word : wordStateMap.entrySet()) {
				for (final STATE state : word.getValue()) {
					for (final OutgoingInternalTransition<LETTER, STATE> transition : mEagerAutomaton
							.getSuccessors(state)) {
						final STATE succ = transition.getSucc();

						if (missingStates.remove(succ)) {

							final ArrayList<LETTER> newWord = new ArrayList<>(word.getKey());
							newWord.add(transition.getLetter());
							if (succ.equals(hondaState)) {
								return newWord;
							}

							temp.computeIfAbsent(newWord, x -> new HashSet<>());
							temp.get(newWord).add(succ);
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
	private RabinAutomaton<LETTER, STATE> getSuffixAutomaton(final RabinAutomaton<LETTER, STATE> automaton) {

		final RabinAutomaton<LETTER, STATE> nonReducedAutomaton =
				new RabinAutomaton<>(automaton.getAlphabet(), automaton.getStates(), automaton.getAcceptingStates(),
						automaton.getAcceptingStates(), automaton.getFiniteStates(), automaton.getTransitions());
		final RabinAutomaton<LETTER, STATE> result =
				RabinAutomataUtils.eagerAutomaton(nonReducedAutomaton, automaton.getFiniteStates());

		return result;

	}

	private List<LETTER> getStem(final STATE hondaState) throws AutomataOperationCanceledException {
		final HashSet<STATE> exploredStates = new HashSet<>();
		HashMap<List<LETTER>, HashSet<STATE>> wordStateMap = new HashMap<>();
		final HashSet<STATE> initialSet = new HashSet<>();
		mEagerAutomaton.getInitialStates().forEach(x -> initialSet.add(x));
		wordStateMap.put(new ArrayList<LETTER>(), initialSet);

		while (!isCancellationRequested()) {
			final HashMap<List<LETTER>, HashSet<STATE>> temp = new HashMap<>();

			for (final Entry<List<LETTER>, HashSet<STATE>> word : wordStateMap.entrySet()) {
				for (final STATE state : word.getValue()) {
					for (final OutgoingInternalTransition<LETTER, STATE> transition : mEagerAutomaton
							.getSuccessors(state)) {
						final STATE succ = transition.getSucc();

						if (exploredStates.add(succ)) {

							final ArrayList<LETTER> newWord = new ArrayList<>(word.getKey());
							newWord.add(transition.getLetter());
							if (succ.equals(hondaState)) {
								return newWord;
							}

							temp.computeIfAbsent(newWord, x -> new HashSet<>());
							temp.get(newWord).add(succ);
						}
					}
				}
			}
			wordStateMap = temp;
		}
		throw new AutomataOperationCanceledException(getClass());
	}

	@Override
	public boolean checkResult(final CRSF stateFactory) throws AutomataOperationCanceledException {
		boolean result = true;
		if (Boolean.FALSE.equals(mResult)) {
			final NestedLassoWord<LETTER> counterExample = getCounterexample();
			result = new Accepts<>(mServices, mEagerAutomaton, counterExample).getResult();
		}
		return result;
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
	public class RabinSuccessorProvider implements ISuccessorProvider<STATE> {

		private final IRabinAutomaton<LETTER, STATE> mAutomaton;

		RabinSuccessorProvider(final IRabinAutomaton<LETTER, STATE> automaton) {
			mAutomaton = automaton;
		}

		public <E extends IOutgoingTransitionlet<LETTER, STATE>> Iterator<STATE>
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
}
