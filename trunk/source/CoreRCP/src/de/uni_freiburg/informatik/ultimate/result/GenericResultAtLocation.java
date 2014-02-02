package de.uni_freiburg.informatik.ultimate.result;

import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * Object for all results for which ULTIMATE does not offer a special result class.
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <P>
 */
public class GenericResultAtLocation extends AbstractResult implements IResultWithSeverity, IResultWithLocation  {

	private final ILocation m_Location;
	private final String m_ShortDescription;
	private final String m_LongDescription;
	private final Severity m_Severity;
	

	public GenericResultAtLocation(String plugin, ILocation location, 
			String shortDescription, String longDescription,
			Severity severity) {
		super(plugin);
		if (location == null) {
			throw new IllegalArgumentException();
		} else {
			m_Location = location;
		}
		m_ShortDescription = shortDescription;
		m_LongDescription = longDescription;
		m_Severity = severity;
	}

	@Override
	public String getShortDescription() {
		return m_ShortDescription;
	}

	@Override
	public String getLongDescription() {
		return m_LongDescription;
	}

	public Severity getSeverity() {
		return m_Severity;
	}

	@Override
	public ILocation getLocation() {
		return m_Location;
	}

}
