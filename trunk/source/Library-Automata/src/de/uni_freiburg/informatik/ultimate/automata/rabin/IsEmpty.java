package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class IsEmpty<LETTER, STATE, CRSF extends IStateFactory<STATE>> extends GeneralOperation<LETTER, STATE, CRSF> {

	private final Boolean mResult;
	private final EagerRabinAutomaton<LETTER, STATE> mEagerAutomaton;
	private final Set<STATE> mEvidence;

	final AutomatonSccComputation<LETTER, STATE> acceptingSccComputation;

	public IsEmpty(final AutomataLibraryServices services, final IRabinAutomaton<LETTER, STATE> automaton) {
		super(services);

		if (EagerRabinAutomaton.class == automaton.getClass()) {
			mEagerAutomaton = (EagerRabinAutomaton<LETTER, STATE>) automaton;
		} else {
			mEagerAutomaton = new EagerRabinAutomaton<>(automaton);
			// Reduces the automaton to its traversable core
		}

		acceptingSccComputation =
				new AutomatonSccComputation<>(services, getStemlessNonFiniteAutomaton(mEagerAutomaton));

		mResult = acceptingSccComputation.getBalls().isEmpty();
		if (!mResult) {
			mEvidence = acceptingSccComputation.getExampleBall();
		} else {
			mEvidence = new HashSet<>();
		}

	}

	@Override
	public Boolean getResult() {
		// TODO Auto-generated method stub
		return mResult;
	}

	public Pair<List<LETTER>, List<LETTER>> getCounterexample() throws AutomataOperationCanceledException {
		List<LETTER> stem = null;
		List<LETTER> loop = null;

		if (!mEvidence.isEmpty()) {
			final Collection<STATE> possibleHondaStates = new ArrayList<>(mEvidence);
			possibleHondaStates.removeIf(x -> !mEagerAutomaton.isAccepting(x));
			final STATE hondaState = possibleHondaStates.iterator().next();

			loop = getLoop(hondaState);
			stem = getStem(hondaState);
		}
		return new Pair<>(stem, loop);
	}

	private List<LETTER> getLoop(final STATE hondaState) throws AutomataOperationCanceledException {

		// get one random accepting State from
		final HashSet<STATE> initialSet = new HashSet<>(); // evidence
		initialSet.add(hondaState);

		final HashSet<STATE> missingStates = new HashSet<>(mEvidence);

		HashMap<List<LETTER>, HashSet<STATE>> wordStateMap = new HashMap<>();
		wordStateMap.put(new ArrayList<>(), initialSet);

		while (!isCancellationRequested()) {

			final HashMap<List<LETTER>, HashSet<STATE>> temp = new HashMap<>();
			for (final List<LETTER> word : wordStateMap.keySet()) {
				for (final STATE state : wordStateMap.get(word)) {
					for (final OutgoingInternalTransition<LETTER, STATE> transition : mEagerAutomaton
							.getSuccessors(state)) {
						final STATE succ = transition.getSucc();
						if (missingStates.contains(succ)) {
							missingStates.remove(succ);
							final ArrayList<LETTER> newWord = new ArrayList<>(word);
							newWord.add(transition.getLetter());
							if (!temp.containsKey(newWord)) {
								temp.put(newWord, new HashSet<>());
							}
							if (succ.equals(hondaState)) {

								return newWord;
							}
							temp.get(newWord).add(succ);
						}
					}
				}
			}
			wordStateMap = temp;
		}
		throw new AutomataOperationCanceledException(getClass());
	}

	private EagerRabinAutomaton<LETTER, STATE>
			getStemlessNonFiniteAutomaton(final EagerRabinAutomaton<LETTER, STATE> automaton) {
		final RabinAutomaton<LETTER, STATE> stemlessAutomaton =
				new RabinAutomaton<>(automaton.getAlphabet(), automaton.getStates(), automaton.getAcceptingStates(),
						automaton.getAcceptingStates(), automaton.getFiniteStates(), automaton.getTransitions());
		final EagerRabinAutomaton<LETTER, STATE> result = new EagerRabinAutomaton<>(stemlessAutomaton, false);
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

			for (final List<LETTER> word : wordStateMap.keySet()) {
				for (final STATE state : wordStateMap.get(word)) {
					for (final OutgoingInternalTransition<LETTER, STATE> transition : mEagerAutomaton
							.getSuccessors(state)) {
						final STATE succ = transition.getSucc();
						if (!exploredStates.contains(succ)) {
							exploredStates.add(succ);
							final ArrayList<LETTER> newWord = new ArrayList<>(word);
							newWord.add(transition.getLetter());
							if (!temp.containsKey(newWord)) {
								temp.put(newWord, new HashSet<>());
							}
							if (succ.equals(hondaState)) {
								return newWord;
							}
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
		if (!mResult) {
			final Pair<List<LETTER>, List<LETTER>> counterExample = getCounterexample();
			result = new Accepts<>(mServices, mEagerAutomaton, counterExample.getFirst(), counterExample.getSecond())
					.getResult();
		}
		return result;
	}

}
