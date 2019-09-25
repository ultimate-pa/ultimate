package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent.reduction;

/**
 * An independence relation that is used in Partial Order or Lipton reductions.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * 
 * @param <STATE> The type of states the independence may depend on.
 * @param <LETTER> The type of letters whose independence is defined by the relation.
 */
public interface IIndependenceRelation<STATE, LETTER> {
	/**
	 * Indicates whether this relation is symmetric (i.e., captures full commutativity)
	 * or not (i.e., captures semicommutativity, Lipton movers).
	 */
	boolean isSymmetric();
	
	/**
	 * Indicates whether this relation is conditional, i.e., the result of {@link contains}
	 * may differ depending on the given states.
	 */
	boolean isConditional();
	
	/**
	 * Tests if the given pair of actions is in the relation for the given state.
	 * Undetermined checks should return {@code false} to remain conservative.
	 * Unconditional relations (see {@link isConditional}) should accept {@code null} as state.
	 */
	boolean contains(STATE state, LETTER a, LETTER b);
}
