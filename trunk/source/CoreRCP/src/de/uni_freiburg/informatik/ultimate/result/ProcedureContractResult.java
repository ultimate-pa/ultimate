package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;



/**
 * Result to store that at a contract holds. The property is given
 * as a Boogie Expression.
 * @author Markus Lindenmann
 * @author Stefan Wissert
 * @author Oleksii Saukh
 * @author Matthias Heizmann
 * @date 02.01.2012
 */
public class ProcedureContractResult<P, E> extends AbstractResult<P> implements IResult {
	
	
	private final ILocation m_Location;
	private String longDescription;
	private E invariant;
	private final String m_ProcedureName;
	
	/**
	 * Constructor.
	 * @param location the Location
	 */
	public ProcedureContractResult(P position, String plugin, 
			List<ITranslator<?,?,?,?>> translatorSequence, 
			ILocation location, String procedureName) {
		super(position, plugin, translatorSequence);
		this.m_Location = location;
		this.m_ProcedureName = procedureName;
		this.longDescription = new String();
		this.invariant = null;
	}
	
	/**
	 * Getter for invariant.
	 * @return the invariant
	 */
	public E getInvariant() {
		return invariant;
	}

	/**
	 * Setter for invariant.
	 * @param invariant the invariant to set
	 */
	public void setInvariant(E invariant) {
		this.invariant = invariant;
	}

	/**
	 * Setter for long description.
	 * @param longDescription the longDescription to set
	 */
	public void setLongDescription(String longDescription) {
		this.longDescription = longDescription;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.result.IResultNode#getLocation()
	 */
	@Override
	public ILocation getLocation() {
		return m_Location;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.result.IResultNode#getShortDescription()
	 */
	@Override
	public String getShortDescription() {
		return "Procedure Contract for " + m_ProcedureName;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.result.IResultNode#getLongDescription()
	 */
	@Override
	public String getLongDescription() {
//		StringBuffer sb = new StringBuffer(longDescription);
//		sb.append(System.getProperty("line.separator"));
//		sb.append("We found an Invariant:");
//		sb.append(System.getProperty("line.separator"));
//		// TODO Should be somehow human readable!
//		if (invariant != null) {
//			sb.append(invariant.toString());
//		}
//		return sb.toString();
		return longDescription;
	}
}
