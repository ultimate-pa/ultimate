package de.uni_freiburg.informatik.ultimate.result;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

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
public class CounterExampleResult<ELEM extends IElement, E> extends AbstractResultAtElement<ELEM> implements IResultWithTrace {
	private final Check m_CheckedSpecification;
	private String longDescription;
	private final List<ILocation> failurePath;
	private final IValuation valuation;

	/**
	 * Constructor.
	 * 
	 * @param location
	 *            the location
	 * @param valuation
	 *            the valuation
	 */
	public CounterExampleResult(ELEM position, String plugin, 
			List<ITranslator<?,?,?,?>> translatorSequence, IProgramExecution<ELEM, E> pe,
			List<ILocation> failurePath,
			IValuation valuation) {
		super(position, plugin, translatorSequence);
		m_CheckedSpecification = ResultUtil.getCheckedSpecification(position);
		this.longDescription = new String();
		this.failurePath = failurePath;
//		this.failurePath = getLocationSequence(pe);
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
	 * Setter for long description.
	 * 
	 * @param longDescription
	 *            the longDescription to set
	 */
	public void setLongDescription(String longDescription) {
		this.longDescription = longDescription;
	}

	@Override
	public String getShortDescription() {
		if (m_CheckedSpecification == null) {
			return "some specification holds - ERROR (information lost during translation process)";
		} else {
			return m_CheckedSpecification.getNegativeMessage();
		}
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
//		sb.append(System.getProperty("line.separator"));
		sb.append("We found a FailurePath: "
				+ System.getProperty("line.separator"));
		sb.append(longDescription);
//		for (ILocation loc : failurePath) {
//			// TODO: What to show exactly here
//			sb.append(loc.toString());
//			sb.append(System.getProperty("line.separator"));
//		}
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
	
	
	public static <TE extends IElement, E> List<ILocation> getLocationSequence(IProgramExecution<TE, E> pe) {
		List<ILocation> result = new ArrayList<ILocation>();
		for (int i=0; i<pe.getLength(); i++) {
			TE te = pe.getTraceElement(i);
			result.add(te.getPayload().getLocation());
		}
		return result;
	}
	
}
