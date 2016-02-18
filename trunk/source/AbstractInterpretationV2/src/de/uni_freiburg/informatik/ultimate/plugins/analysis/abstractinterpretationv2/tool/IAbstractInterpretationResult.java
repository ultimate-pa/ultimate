package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool;

import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface IAbstractInterpretationResult<STATE, ACTION, VARDECL, LOCATION> {

	Map<LOCATION, Term> getLoc2Term();
	
	Set<Term> getTerms();

	List<AbstractCounterexample<STATE, ACTION, VARDECL, LOCATION>> getCounterexamples();

	boolean hasReachedError();

}
