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
	private final EagerRabinAutomaton<LETTER, STATE> eagerAutomaton;
	private final Set<STATE> evidence;

	final AutomatonSccComputation<LETTER, STATE> acceptingSccComputation;

	public IsEmpty(final AutomataLibraryServices services, final IRabinAutomaton<LETTER, STATE> automaton) {
		super(services);

		if (EagerRabinAutomaton.class == automaton.getClass()) {
			eagerAutomaton = (EagerRabinAutomaton<LETTER, STATE>) automaton;
		} else {
			eagerAutomaton = new EagerRabinAutomaton<>(automaton);
			// Reduces the automaton to its traversable core
		}

		acceptingSccComputation =
				new AutomatonSccComputation<>(services, eagerAutomaton.getStemlessNonFiniteAutomaton());

		mResult = acceptingSccComputation.getBalls().isEmpty();
		if (!mResult) {
			evidence = acceptingSccComputation.getExampleBall();
		} else {
			evidence = new HashSet<>();
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
		if (!evidence.isEmpty()) {

			final Collection<STATE> possibleHondaStates = new ArrayList<>(evidence);
			possibleHondaStates.removeIf(x -> !eagerAutomaton.isAccepting(x));
			final STATE hondaState = possibleHondaStates.iterator().next();// get one random accepting State from
			final HashSet<STATE> initialSet = new HashSet<>(); // evidence
			initialSet.add(hondaState);

			final HashSet<STATE> missingStates = new HashSet<>(evidence);

			HashMap<List<LETTER>, HashSet<STATE>> wordStateMap = new HashMap<>();
			wordStateMap.put(new ArrayList<>(), initialSet);

			loopComputation: while (true) {
				if (isCancellationRequested()) {
					throw new AutomataOperationCanceledException(getClass());
				}
				final HashMap<List<LETTER>, HashSet<STATE>> temp = new HashMap<>();
				for (final List<LETTER> word : wordStateMap.keySet()) {
					for (final STATE state : wordStateMap.get(word)) {
						for (final OutgoingInternalTransition<LETTER, STATE> transition : eagerAutomaton
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
									loop = newWord;
									break loopComputation;
								}
								temp.get(newWord).add(succ);
							}
						}
					}
				}
				wordStateMap = temp;
			}

			final HashSet<STATE> exploredStates = new HashSet<>();
			wordStateMap.clear();
			initialSet.clear();
			eagerAutomaton.getInitialStates().forEach(x -> initialSet.add(x));
			wordStateMap.put(new ArrayList<LETTER>(), initialSet);

			stemComputation: while (true) {
				if (isCancellationRequested()) {
					throw new AutomataOperationCanceledException(getClass());
				}
				final HashMap<List<LETTER>, HashSet<STATE>> temp = new HashMap<>();

				for (final List<LETTER> word : wordStateMap.keySet()) {
					for (final STATE state : wordStateMap.get(word)) {
						for (final OutgoingInternalTransition<LETTER, STATE> transition : eagerAutomaton
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
									stem = newWord;
									break stemComputation;
								}
								temp.get(newWord).add(succ);
							}
						}
					}
				}
				wordStateMap = temp;
			}
		}
		return new Pair<>(stem, loop);
	}

	@Override
	public boolean checkResult(final CRSF stateFactory) throws AutomataOperationCanceledException {
		boolean result = true;
		if (!mResult) {
			final Pair<List<LETTER>, List<LETTER>> counterExample = this.getCounterexample();
			result = new Accepts<>(mServices, eagerAutomaton, counterExample.getFirst(), counterExample.getSecond())
					.getResult();
		}
		return result;
	}

}
