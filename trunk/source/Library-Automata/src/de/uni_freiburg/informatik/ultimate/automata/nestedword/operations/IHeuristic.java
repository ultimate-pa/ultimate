package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import java.util.List;
import java.util.Map;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 *            Type of states
 * @param <LETTER>
 *            Type of transitions
 */
public interface IHeuristic<STATE, LETTER> {

	double getHeuristicValue(STATE state, STATE stateK, LETTER trans);

	int getConcreteCost(LETTER trans);

	static <STATE, LETTER> IHeuristic<STATE, LETTER> getZeroHeuristic() {
		return new IHeuristic<STATE, LETTER>() {
			@Override
			public final double getHeuristicValue(final STATE state, final STATE stateK, final LETTER trans) {
				return 0.0;
			}

			@Override
			public final int getConcreteCost(final LETTER e) {
				return 1;
			}

			@Override
			public Map<IsEmptyHeuristic<LETTER, STATE>.Item, Integer> compareSuccessors(final List<IsEmptyHeuristic<LETTER, STATE>.Item> successors) {
				throw new UnsupportedOperationException("Not implemented for this heuristic");
			}
		};
	}

	Map<IsEmptyHeuristic<LETTER, STATE>.Item, Integer> compareSuccessors(List<IsEmptyHeuristic<LETTER, STATE>.Item> successors);


}
