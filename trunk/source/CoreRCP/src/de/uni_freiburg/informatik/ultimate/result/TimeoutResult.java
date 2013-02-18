package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;

public class TimeoutResult<P> extends AbstractResult<P> implements IResult{
	
	
	private ILocation m_Location;
	private String m_shortDescription;
	private String m_longDescription;


	public TimeoutResult(P position, String plugin, 
			List<ITranslator<?,?,?,?>> translatorSequence, ILocation location) {
		super(position, plugin, translatorSequence);
		this.m_Location = location;
		this.m_shortDescription = new String();
		this.m_longDescription = new String();
	}
	
	@Override
	public ILocation getLocation() {
		return m_Location;
	}

	@Override
	public String getShortDescription() {
		return m_shortDescription;
	}

	@Override
	public String getLongDescription() {
		return m_longDescription;
	}
	
	
	/**
	 * Setter for the short description.
	 * @param shortDescription the shortDescription to set
	 */
	public void setShortDescription(String shortDescription) {
		this.m_shortDescription = shortDescription;
	}

	/**
	 * Setter for long description.
	 * @param longDescription the longDescription to set
	 */
	public void setLongDescription(String longDescription) {
		this.m_longDescription = longDescription;
	}

	
}
