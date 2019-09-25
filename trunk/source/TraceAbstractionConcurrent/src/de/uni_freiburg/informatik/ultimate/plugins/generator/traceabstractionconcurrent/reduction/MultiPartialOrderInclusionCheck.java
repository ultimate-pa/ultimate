package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent.reduction;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
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
 * @param <LETTER>
 */
public class MultiPartialOrderInclusionCheck<LETTER> {
	private final IIndependenceRelation<Set<IPredicate>, LETTER>[] mRelations;
	private final INestedWordAutomaton<LETTER, IPredicate> mProgram;
	private final INestedWordAutomaton<LETTER, IPredicate> mProof;
	private final List<LETTER> mCounterexample;

	public MultiPartialOrderInclusionCheck(final IIndependenceRelation<Set<IPredicate>, LETTER>[] relations,
			final INestedWordAutomaton<LETTER, IPredicate> program,
			final INestedWordAutomaton<LETTER, IPredicate> proof) {
		mRelations = relations;
		mProgram = program;
		mProof = proof;

		mCounterexample = performCheck();
	}

	private final List<LETTER> performCheck() {
		final Pair<List<LETTER>, Integer> result = search(mProgram.getInitialStates(), mProof.getInitialStates(),
				Collections.emptyMap());
		return result.getFirst();
	}

	private final Pair<List<LETTER>, Integer> search(final Set<IPredicate> location, final Set<IPredicate> predicate,
			final Map<LETTER, Integer> sleepSet) {
		final int maxLevel = mRelations.length - 1;

		if (predicate.stream().anyMatch(mProof::isFinal)) {
			return new Pair<>(null, maxLevel);
		} else if (location.stream().anyMatch(mProgram::isFinal)) {
			return new Pair<>(Arrays.asList(), maxLevel);
		}

		final Set<LETTER> enabledActions = location.stream().flatMap(l -> mProgram.lettersInternal(l).stream())
				.collect(Collectors.toSet());
		int level = maxLevel;

		for (LETTER a : enabledActions) {
			if (sleepSet.containsKey(a)) {
				final Integer sleepLevel = sleepSet.get(a);
				assert sleepLevel != null;
				level = Math.min(level, sleepLevel);

			} else {
				// TODO: there must be a much better way than this, this is horrible
				final Set<IPredicate> nextLocation = location.stream()
						.flatMap(l -> StreamSupport.stream(mProgram.internalSuccessors(l, a).spliterator(), false))
						.map(OutgoingInternalTransition::getSucc).collect(Collectors.toSet());
				final Set<IPredicate> nextPredicate = predicate.stream()
						.flatMap(phi -> StreamSupport.stream(mProof.internalSuccessors(phi, a).spliterator(), false))
						.map(OutgoingInternalTransition::getSucc).collect(Collectors.toSet());

				final Map<LETTER, Integer> nextSleep = recomputeSleep(sleepSet, predicate, a);
				final Pair<List<LETTER>, Integer> result = search(nextLocation, nextPredicate, nextSleep);

				final Integer recursiveLevel = result.getSecond();
				assert recursiveLevel != null;
				level = Math.min(level, recursiveLevel);
				sleepSet.put(a, recursiveLevel);

				if (result.getFirst() != null) {
					result.getFirst().add(a);
					return new Pair<>(result.getFirst(), level);
				}
			}
		}

		return new Pair<>(null, level);
	}

	private final Map<LETTER, Integer> recomputeSleep(final Map<LETTER, Integer> oldSleepSet,
			final Set<IPredicate> context, final LETTER action) {
		final Map<LETTER, Integer> newSleepSet = new HashMap<>(oldSleepSet.size());

		for (Map.Entry<LETTER, Integer> entry : oldSleepSet.entrySet()) {
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

	/**
	 * @return The result of the inclusion check: {@code true} if the program is
	 *         guaranteed to be covered by the proof, {@code false} otherwise.
	 */
	public boolean isIncluded() {
		return mCounterexample == null;
	}

	/**
	 * Retrieves the counterexample found during the search, if any. This is a
	 * sequence of letters leading from the program's initial location to an error
	 * location. The sequence is guaranteed not to be accepted by the proof
	 * automaton.
	 */
	public List<LETTER> getCounterexample() {
		return mCounterexample;
	}
}
