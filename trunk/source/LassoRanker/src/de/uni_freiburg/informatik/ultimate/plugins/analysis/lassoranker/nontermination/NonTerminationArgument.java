package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.nontermination;

import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.IResult;


/**
 * Represents a non-termination argument in form of an infinite execution
 * of the lasso program. It is composed of
 * 
 * <ul>
 * <li> an execution of the stem, i.e., up until the first node occuring
 *   infinitely often,
 * <li> an execution of the loop, and
 * <li> a recurrent set.
 * </ul>
 * 
 * @author Jan Leike
 */
public class NonTerminationArgument implements IResult {
	
	private IProgramExecution m_stem_execution;
	private IProgramExecution m_loop_execution;
	private RecurrentSet m_recurrent_set;
	
	@Override
	public ILocation getLocation() {
		// TODO Auto-generated method stub
		return null;
	}
	@Override
	public String getShortDescription() {
		// TODO Auto-generated method stub
		return null;
	}
	@Override
	public String getLongDescription() {
		// TODO Auto-generated method stub
		return null;
	}
}
