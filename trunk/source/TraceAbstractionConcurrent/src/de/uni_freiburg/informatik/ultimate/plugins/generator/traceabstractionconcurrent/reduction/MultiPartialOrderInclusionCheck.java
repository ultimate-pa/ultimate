package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent.reduction;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Employs a modified sleep set algorithm to check if a given proof is
 * sufficient to prove a given program correct. A proof is considered
 * sufficient, if its closure under a sequence of independence relations
 * contains the program.
 *
 * As this problem is undecidable, the check implemented here is sound but not
 * complete: Even when a counterexample is found, the proof might actually have
 * been sufficient.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <STATE1>
 * @param <STATE2>
 * @param <LETTER>
 */
public class MultiPartialOrderInclusionCheck<STATE1, STATE2, LETTER> {
	private final IIndependenceRelation<STATE2, LETTER>[] mRelations;
	private final INestedWordAutomaton<LETTER, STATE1> mProgram;
	private final INestedWordAutomaton<LETTER, STATE2> mProof;
	private final NestedRun<LETTER, STATE1> mCounterexample;

	public MultiPartialOrderInclusionCheck(final IIndependenceRelation<STATE2, LETTER>[] relations,
			final INestedWordAutomaton<LETTER, STATE1> program, final INestedWordAutomaton<LETTER, STATE2> proof) {
		mRelations = relations;
		mProgram = program;
		mProof = proof;

		assert NestedWordAutomataUtils.isFiniteAutomaton(program) : "POR does not support calls and returns.";
		assert NestedWordAutomataUtils.isFiniteAutomaton(proof) : "POR does not support calls and returns.";

		mCounterexample = performCheck();
	}

	/**
	 * @return The result of the inclusion check: {@code true} if the program is
	 *         guaranteed to be covered by the proof, {@code false} otherwise.
	 */
	public boolean getResult() {
		return mCounterexample == null;
	}

	/**
	 * Retrieves the counterexample found during the search, if any. This is an
	 * automaton run leading from the program's initial location to an error
	 * location. The corresponding word is guaranteed not to be accepted by the
	 * proof automaton.
	 */
	public NestedRun<LETTER, STATE1> getCounterexample() {
		return mCounterexample;
	}

	private final NestedRun<LETTER, STATE1> performCheck() {
		final Pair<List<LETTER>, Integer> result = search(getInitial(mProgram), getInitial(mProof),
				Collections.emptyMap());
		final List<LETTER> symbols = result.getFirst();
		if (symbols != null) {
			return createRun(symbols);
		}
		return null;
	}

	private final Pair<List<LETTER>, Integer> search(final STATE1 location, final STATE2 predicate,
			final Map<LETTER, Integer> sleepSet) {
		final int maxLevel = mRelations.length - 1;

		if (mProof.isFinal(predicate)) {
			// Assumes the final state of mProof is a sink state.
			// Hence we can abort the search here.
			return new Pair<>(null, maxLevel);
		} else if (mProgram.isFinal(location)) {
			// A counterexample has been found.
			return new Pair<>(Arrays.asList(), maxLevel);
		}

		final Set<LETTER> enabledActions = mProgram.lettersInternal(location);
		int level = maxLevel;

		for (final LETTER a : enabledActions) {
			if (sleepSet.containsKey(a)) {
				final Integer sleepLevel = sleepSet.get(a);
				assert sleepLevel != null;
				level = Math.min(level, sleepLevel);
			} else {
				final STATE1 nextLocation = getSuccessor(mProgram, location, a);
				final STATE2 nextPredicate = getSuccessor(mProof, predicate, a);

				final Map<LETTER, Integer> nextSleep = recomputeSleep(sleepSet, predicate, a);
				final Pair<List<LETTER>, Integer> result = search(nextLocation, nextPredicate, nextSleep);

				final Integer recursiveLevel = result.getSecond();
				assert recursiveLevel != null;
				level = Math.min(level, recursiveLevel);
				sleepSet.put(a, recursiveLevel);

				final List<LETTER> counterexample = result.getFirst();
				if (counterexample != null) {
					counterexample.add(a);
					return new Pair<>(counterexample, level);
				}
			}
		}

		return new Pair<>(null, level);
	}

	private final Map<LETTER, Integer> recomputeSleep(final Map<LETTER, Integer> oldSleepSet, final STATE2 context,
			final LETTER action) {
		final Map<LETTER, Integer> newSleepSet = new HashMap<>(oldSleepSet.size());

		for (final Map.Entry<LETTER, Integer> entry : oldSleepSet.entrySet()) {
			for (int level = entry.getValue(); level >= 0; level--) {
				assert 0 <= level && level < mRelations.length : "Illegal level " + level;
				if (mRelations[level].contains(context, entry.getKey(), action)) {
					newSleepSet.put(entry.getKey(), level);
					break;
				}
			}
		}

		return newSleepSet;
	}

	private NestedRun<LETTER, STATE1> createRun(final List<LETTER> symbols) {
		// The search returns the word in reverse order.
		Collections.reverse(symbols);

		final Word<LETTER> word = new Word<>((LETTER[]) symbols.toArray());
		final NestedWord<LETTER> nestedWord = NestedWord.nestedWord(word);

		final ArrayList<STATE1> stateSequence = new ArrayList<>(word.length() + 1);
		STATE1 current = getInitial(mProgram);
		stateSequence.add(current);
		for (final LETTER a : word) {
			current = getSuccessor(mProgram, current, a);
			stateSequence.add(current);
		}

		return new NestedRun<>(nestedWord, stateSequence);
	}

	// TODO: determinize automata, use built-in product automata
	private static <STATE> STATE getInitial(final INestedWordAutomaton<?, STATE> automaton) {
		final Set<STATE> initial = automaton.getInitialStates();
		assert initial.size() == 1 : "Automaton must be deterministic";
		return initial.iterator().next();
	}

	private <STATE> STATE getSuccessor(final INestedWordAutomaton<LETTER, STATE> automaton, final STATE state,
			final LETTER letter) {
		// TODO: there must be a much better way than this, this is horrible
		final Set<STATE> successors = StreamSupport
				.stream(automaton.internalSuccessors(state, letter).spliterator(), false)
				.map(OutgoingInternalTransition::getSucc).collect(Collectors.toSet());
		assert successors.size() == 1 : "Automaton must be deterministic";
		return successors.iterator().next();
	}
}
