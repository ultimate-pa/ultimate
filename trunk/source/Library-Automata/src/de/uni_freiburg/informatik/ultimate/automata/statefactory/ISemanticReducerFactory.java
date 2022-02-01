package de.uni_freiburg.informatik.ultimate.automata.statefactory;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public interface ISemanticReducerFactory<STATE, LETTER> extends IStateFactory<STATE> {

	/**
	 * Filter out semantically redundant states.
	 * @param states A collection of states.
	 * @return A collection of filtered states
	 */
	Iterable<STATE> filter(final Iterable<STATE> states);


	// STATE getOptimalDestination(final List<STATE> src, final LETTER letter, final Set<STATE> dest);

	/**
	 *
	 * @param states
	 * @param src
	 * @param letter
	 * @param dest
	 * 			FIXME: looks like dest parameter might be redundant, as it always is a subset of states, in our
	 *   			applications (Mostafa, Alex, 17.1.2018)
	 *     			possible reason to keep the parameter: if a future implementation needs the original set of
	 *     			successors/destinations
	 *     		Mostafa: DummySemanticReducer is using the destination states, so we can keep it in the interface
	 * @return
	 */
	Iterable<STATE> getOptimalDestination(final Iterable<STATE> states,
			final List<STATE> src, final LETTER letter, final Iterable<STATE> dest);

	/***
	 * Reduce a set of rules using the provided filtering states method.
	 * @param oldRules
	 * @return
	 */
	default <LETTER extends IRankedLetter> Iterable<TreeAutomatonRule<LETTER, STATE>> reduceRules(
			final Iterable<TreeAutomatonRule<LETTER, STATE>> oldRules) {

		final NestedMap2<List<STATE>, LETTER, Set<STATE>> strongRules = new NestedMap2<>();
		for (final TreeAutomatonRule<LETTER, STATE> rule : oldRules) {
			if (strongRules.get(rule.getSource(), rule.getLetter()) == null) {
				strongRules.put(rule.getSource(), rule.getLetter(), new HashSet<>());
			}
			strongRules.get(rule.getSource(), rule.getLetter()).add(rule.getDest());
		}
		final Set<TreeAutomatonRule<LETTER, STATE>> newRules = new HashSet<>();
		for (final Triple<List<STATE>, LETTER, Set<STATE>> triple : strongRules.entrySet()) {
			for (final STATE destination : filter(triple.getThird())) {
				newRules.add(new TreeAutomatonRule<LETTER, STATE>(triple.getSecond(), triple.getFirst(), destination));
			}
		}
		return newRules;
	}

}
