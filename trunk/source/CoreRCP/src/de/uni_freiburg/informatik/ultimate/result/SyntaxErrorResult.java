package de.uni_freiburg.informatik.ultimate.result;

import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * Report a syntax error that has been detected.
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class SyntaxErrorResult extends AbstractResult 
												implements IResultWithLocation {
	
	private String m_LongDescription;
	private final ILocation m_Location;

	public SyntaxErrorResult(String plugin, 
			ILocation location,
			String longDescription) {
		super(plugin);
		m_Location = location;
		m_LongDescription = longDescription;
	}

	@Override
	public String getShortDescription() {
		return "Incorrect Syntax";
	}

	@Override
	public String getLongDescription() {
		return m_LongDescription;
	}

	@Override
	public ILocation getLocation() {
		return m_Location;
	}

	
}