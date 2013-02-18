package de.uni_freiburg.informatik.ultimate.result;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;

/**
 * Result to store that the specification given at some location does not always
 * holds. We also store a computerexample to the correctness of the
 * specification. This counterexample is given as list of locations. (Locations
 * of Statements which lead to a state that violates the specification.  
 * @author Markus Lindenmann
 * @author Stefan Wissert
 * @author Oleksii Saukh
 * @date 02.01.2012
 */
public class CounterExampleResult<P> extends AbstractResult<P> implements IResultWithTrace {
	private ILocation m_Location;
	private String shortDescription;
	private String longDescription;
	private List<ILocation> failurePath;
	private IValuation valuation;

	/**
	 * Constructor.
	 * 
	 * @param location
	 *            the location
	 * @param valuation
	 *            the valuation
	 */
	public CounterExampleResult(P position, String plugin, 
			List<ITranslator<?,?,?,?>> translatorSequence, ILocation location, 
			IValuation valuation) {
		super(position, plugin, translatorSequence);
		this.m_Location = location;
		this.shortDescription = new String();
		this.longDescription = new String();
		this.failurePath = new ArrayList<ILocation>();
		this.valuation = valuation;
	}

	/**
	 * Getter for the valuation.
	 * 
	 * @return the valuation
	 */
	public IValuation getValuation() {
		return valuation;
	}

	/**
	 * Setter for the valuation.
	 * 
	 * @param valuation
	 *            the valuation
	 */
	public void setValuation(IValuation valuation) {
		this.valuation = valuation;
	}

	/**
	 * Setter for Location.
	 * 
	 * @param location
	 *            the Location to set
	 */
	public void setLocation(ILocation location) {
		this.m_Location = location;
	}

	/**
	 * Setter for short description.
	 * 
	 * @param shortDescription
	 *            the shortDescription to set
	 */
	public void setShortDescription(String shortDescription) {
		this.shortDescription = shortDescription;
	}

	/**
	 * Setter for long description.
	 * 
	 * @param longDescription
	 *            the longDescription to set
	 */
	public void setLongDescription(String longDescription) {
		this.longDescription = longDescription;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.result.IResultNode#getLocation()
	 */
	@Override
	public ILocation getLocation() {
		return m_Location;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.result.IResultNode#getShortDescription
	 * ()
	 */
	@Override
	public String getShortDescription() {
		return shortDescription;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.result.IResultNode#getLongDescription
	 * ()
	 */
	@Override
	public String getLongDescription() {
		StringBuilder sb = new StringBuilder();
		sb.append(longDescription);
		sb.append(System.getProperty("line.separator"));
		sb.append("We found a FailurePath: "
				+ System.getProperty("line.separator"));
		for (ILocation loc : failurePath) {
			// TODO: What to show exactly here
			sb.append(loc.toString());
			sb.append(System.getProperty("line.separator"));
		}
		return sb.toString();
	}

	/**
	 * Getter for the failure path.
	 * 
	 * @return the failurePath
	 */
	public List<ILocation> getFailurePath() {
		return failurePath;
	}

	/**
	 * Setter for the failure path.
	 * 
	 * @param failurePath
	 *            the failurePath to set
	 */
	public void setFailurePath(List<ILocation> failurePath) {
		this.failurePath = failurePath;
	}
}
