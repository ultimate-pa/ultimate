package de.uni_freiburg.informatik.ultimate.result;

import java.util.ArrayList;
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
public class UnprovableResult<P extends IElement> extends AbstractResultAtElement<P> implements IResultWithTrace {
	private String shortDescription;
	private String longDescription;
	private List<ILocation> failurePath;
	
	/**
	 * Constructor.
	 * @param location the Location
	 */
	public UnprovableResult(P position, String plugin, 
			List<ITranslator<?,?,?,?>> translatorSequence, ILocation location) {
		super(position, plugin, translatorSequence);
		this.shortDescription = new String();
		this.longDescription = new String();
		this.failurePath = new ArrayList<ILocation>();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.result.IResultNode#getShortDescription()
	 */
	@Override
	public String getShortDescription() {
		return shortDescription;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.result.IResultNode#getLongDescription()
	 */
	@Override
	public String getLongDescription() {
		return longDescription;
	}

	/**
	 * Setter for the short description.
	 * @param shortDescription the shortDescription to set
	 */
	public void setShortDescription(String shortDescription) {
		this.shortDescription = shortDescription;
	}

	/**
	 * Setter for long description.
	 * @param longDescription the longDescription to set
	 */
	public void setLongDescription(String longDescription) {
		this.longDescription = longDescription;
	}

    /**
     * Getter for the failure path.
     * @return the failurePath
     */
    public List<ILocation> getFailurePath() {
        return failurePath;
    }

    /**
     * Setter for the failure path.
     * @param failurePath the failurePath to set
     */
    public void setFailurePath(List<ILocation> failurePath) {
        this.failurePath = failurePath;
    }
}
