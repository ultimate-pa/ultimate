package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;


/**
 * Result to store that we are not able to determine if a specification given at
 * some location holds. 
 * We also provide a potential counterexample for which one of the following
 * holds.
 * <ul>
 * <li> We are not able to determine feasibility of the counterexample. (e.g.,
 * multiplication of variables and LIRA logic, timeout of solver,..)
 * <li> We are not able to exclude the counterexample in the refined 
 * abstraction. (e.g., predicate abstraction with fixed set of predicates)
 * </ul>
 * If the fail of a model checker is not related to one specific counterexample
 * we use the timeout result.
 * @author Markus Lindenmann
 * @author Stefan Wissert
 * @author Oleksii Saukh
 * @date 02.01.2012
 */
public class UnprovableResult<ELEM extends IElement, TE, E> 
			extends AbstractResultAtElement<ELEM> implements IResultWithTrace {
	
	private final Check m_CheckedSpecification;
	private final IProgramExecution<TE, E> m_ProgramExecution;
	
	/**
	 * Constructor.
	 * @param location the Location
	 */
	public UnprovableResult(String plugin, ELEM position,  
			List<ITranslator<?,?,?,?>> translatorSequence, 
			IProgramExecution<TE, E> programExecution) {
		super(position, plugin, translatorSequence);
		m_CheckedSpecification = ResultUtil.getCheckedSpecification(position);
		m_ProgramExecution = programExecution;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.result.IResultNode#getShortDescription()
	 */
	@Override
	public String getShortDescription() {
		return "Unable to prove that " + m_CheckedSpecification;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.result.IResultNode#getLongDescription()
	 */
	@Override
	public String getLongDescription() {
		return "Unable to prove that " + m_CheckedSpecification;
	}

    /**
     * Getter for the failure path.
     * @return the failurePath
     */
    public List<ILocation> getFailurePath() {
        throw new UnsupportedOperationException("not yet implemented");
    }
}
