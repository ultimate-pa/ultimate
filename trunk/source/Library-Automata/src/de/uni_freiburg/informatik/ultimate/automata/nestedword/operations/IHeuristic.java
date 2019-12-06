package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

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
		};
	}

}
