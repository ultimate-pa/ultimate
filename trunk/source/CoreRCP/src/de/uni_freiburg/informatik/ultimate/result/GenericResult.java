package de.uni_freiburg.informatik.ultimate.result;



/**
 * Object for all results for which ULTIMATE does not offer a special result class.
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class GenericResult extends AbstractResult implements IResultWithSeverity {

	private final String m_ShortDescription;
	private final String m_LongDescription;
	private final Severity m_Severity;

	public GenericResult(String plugin, String shortDescription, 
			String longDescription,	Severity severity) {
		super(plugin);
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

}
