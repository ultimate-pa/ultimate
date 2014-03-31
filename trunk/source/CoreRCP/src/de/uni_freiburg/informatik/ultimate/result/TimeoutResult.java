package de.uni_freiburg.informatik.ultimate.result;


/**
 * Use this to report that there was a timeout in cases this timeout is not
 * related to a specific element. (In cases the timout is related to a specific
 * element, e.g., an error location see TimeoutResultAtElement).
 * @author Matthias Heizmann
 *
 * @param <ELEM>
 */
public class TimeoutResult extends AbstractResult implements IResult, ITimeoutResult {
	
	public TimeoutResult(String plugin, String longDescription) {
		super(plugin);
		m_longDescription = longDescription;
	}

	private final String m_longDescription;

	@Override
	public String getShortDescription() {
		return "Timeout";
	}

	@Override
	public String getLongDescription() {
		return m_longDescription;
	}

	
}
