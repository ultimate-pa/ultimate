package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface IAbstractInterpretationResult<STATE, ACTION, VARDECL, LOCATION> {

	Map<LOCATION, Term> getTerms();

	List<AbstractCounterexample<STATE, ACTION, VARDECL, LOCATION>> getCounterexamples();

	boolean hasReachedError();

}
