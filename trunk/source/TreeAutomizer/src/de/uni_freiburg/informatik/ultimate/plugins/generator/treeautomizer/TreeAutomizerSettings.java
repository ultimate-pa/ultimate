package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer;

public class TreeAutomizerSettings {

	/**
	 * Use the class Difference or LazyDifference?
	 * Difference: naive difference algorithm
	 * LazyDifference: smart totalization of right hand side automaton, take only reachable states into consideration.
	 */
	public static final boolean USE_NAIVE_DIFFERENCE = false;

	/**
	 * Introduce edges to the interpolant automaton during or before the difference operation (in refineAbstraction)?
	 */
	public static final boolean GENERALIZE_INTERPOLANT_AUTOMATON_UPFRONT = false;

	/**
	 *
	 * If this is true and GENERALIZE_INTERPOLANT_AUTOMATON_UPFRONT, no generalization of the interpolant automaton is
	 * done (and we thus might not terminate, even with good interpolants).
	 */
	public static final boolean USE_RAW_INTERPOLANT_AUTOMATON = false;

	/**
	 * Upper bound for iterations of CEGAR loop, choose negative value for no bound.
	 */
	public static final int ITERATIONS_BOUND = -1;

	/**
	 * Apply minimization to current abstraction at the end of every CEGAR iteration?
	 */
	public static final TaMinimization MINIMIZATION = TaMinimization.HOPCROFT;

	/***
	 * Use semantic reduction in lazy difference
	 */
	public static final boolean USE_SEMANTIC_REDUCTION = true;
}
