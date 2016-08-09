package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * The result of an abstract interpretation analysis run.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public interface IAbstractInterpretationResult<STATE, ACTION, VARDECL, LOCATION> {

	/**
	 * @return a {@link Map} mapping to each location that was reachable during the analysis the computed fixpoint as
	 *         {@link Term}.
	 */
	Map<LOCATION, Term> getLoc2Term();

	/**
	 * @return a {@link Set} containing all fixpoints computed during the analysis as {@link Term}s.
	 */
	Set<Term> getTerms();

	/**
	 * @return A {@link List} of all (potentially spurious) abstract counterexamples found during the analysis. A
	 *         counterexample is a sequence of ACTIONs from an initial location to an error location. An abstract
	 *         counterexample does not contain the correct number of loop unrollings, but rather the number of loop
	 *         unrollings until a fixpoint was computed.
	 */
	List<AbstractCounterexample<STATE, ACTION, VARDECL, LOCATION>> getCounterexamples();

	/**
	 * @return true if the analysis could reach an error location, false otherwise.
	 */
	boolean hasReachedError();

	/**
	 * Generates a single string that represents this result. The string contains all fixpoints computed during the
	 * analysis.
	 *
	 * @param funSimplify
	 *            A function that takes a {@link Term} as parameter and returns a {@link String} representing the term.
	 * @return A string representing this result.
	 */
	String toSimplifiedString(Function<Term, String> funSimplify);
}
