package de.uni_freiburg.informatik.ultimate.result;
/**
 * Result that says that all specifications were checked and hold.
 * Use this also if there was not specification.
 * 
 * @author Matthias Heizmann
 */
public class AllSpecificationsHoldResult extends AbstractResult {

	private final String m_Longdescription;

	public AllSpecificationsHoldResult(String plugin, String longDescription) {
		super(plugin);
		m_Longdescription = longDescription;
	}

	@Override
	public String getShortDescription() {
		return "All specifications hold";
	}

	@Override
	public String getLongDescription() {
		return m_Longdescription;
	}

}
