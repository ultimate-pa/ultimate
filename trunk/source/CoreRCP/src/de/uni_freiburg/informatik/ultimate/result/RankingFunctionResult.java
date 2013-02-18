package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;


public class RankingFunctionResult<P> extends AbstractResult<P> implements IResult {
	private ILocation m_Location;
	private String m_ShortDescription;
	private String m_LongDescription;

	/**
	 * Constructor.
	 * 
	 * @param location
	 *            the location
	 */
	public RankingFunctionResult(P position, String plugin, 
			List<ITranslator<?,?,?,?>> translatorSequence, ILocation location) {
		super(position, plugin, translatorSequence);
		this.m_Location = location;
		this.m_ShortDescription = new String();
		this.m_LongDescription = new String();
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
		return m_ShortDescription;
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
		return m_LongDescription;
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
		this.m_ShortDescription = shortDescription;
	}

	/**
	 * Setter for long description.
	 * 
	 * @param longDescription
	 *            the longDescription to set
	 */
	public void setLongDescription(String longDescription) {
		this.m_LongDescription = longDescription;
	}
}
