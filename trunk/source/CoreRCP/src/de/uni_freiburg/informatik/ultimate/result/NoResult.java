package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

public class NoResult<P> extends AbstractResult<P> implements IResult {
	private ILocation m_Location;
	private String shortDescription;
	private String longDescription;

	/**
	 * Constructor.
	 * 
	 * @param location
	 *            the location
	 * @param valuation
	 *            the valuation
	 */
	public NoResult(P position, String plugin, 
			List<ITranslator<?,?,?,?>> translatorSequence, ILocation location) {
		super(position, plugin, translatorSequence);
		this.m_Location = location;
		this.shortDescription = new String();
		this.longDescription = new String();
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
		return this.longDescription;
	}


}
