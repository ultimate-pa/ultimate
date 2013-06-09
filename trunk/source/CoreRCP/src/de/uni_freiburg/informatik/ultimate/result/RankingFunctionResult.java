package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;


public class RankingFunctionResult<P> extends AbstractResult<P> implements IResult {
	private final ILocation m_Location;
	private final String m_ShortDescription;
	private final  String m_LongDescription;

	/**
	 * Constructor.
	 * 
	 * @param location
	 *            the location
	 */
	public RankingFunctionResult(P position, String plugin, 
			List<ITranslator<?,?,?,?>> translatorSequence, ILocation location, 
			String shortDescription, String longDescription) {
		super(position, plugin, translatorSequence);
		this.m_Location = location;
		this.m_ShortDescription = shortDescription;
		this.m_LongDescription = longDescription;
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

}
