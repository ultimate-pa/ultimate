package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;

public class PossibleUnsoundnessWarningResult<P> extends AbstractResult<P> {
	
	private ILocation m_Location;
	private String m_ShortDescription;
	private String m_LongDescription;

	public PossibleUnsoundnessWarningResult(P position, String plugin,
			List<ITranslator<?, ?, ?, ?>> translatorSequence, ILocation loc) {
		super(position, plugin, translatorSequence);
		m_ShortDescription = "Possibly Unsound";
		m_Location = loc;
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
		return m_ShortDescription;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.result.IResultNode#getLongDescription()
	 */
	@Override
	public String getLongDescription() {
		return m_LongDescription;
	}

	public void setShortDescription(String shortDescription) {
		this.m_ShortDescription = shortDescription;
	}

	/**
	 * Setter for long description.
	 * @param longDescription the longDescription to set
	 */
	public void setLongDescription(String longDescription) {
		this.m_LongDescription = longDescription;
	}

}
