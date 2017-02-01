package de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences;

import java.util.Map;

public class SpaceExPreferenceGroup {
	
	private final int mId;
	private final Map<String, String> mInitialLocations;
	private final String mInitialVariableInfix;
	
	public SpaceExPreferenceGroup(Map<String, String> initialLocations, String initialVariableInfix, int id) {
		mId = id;
		mInitialLocations = initialLocations;
		mInitialVariableInfix = initialVariableInfix;
	}
	
	public Map<String, String> getInitialLocations() {
		return mInitialLocations;
	}
	
	public String getInitialVariableInfix() {
		return mInitialVariableInfix;
	}
	
	public int getId() {
		return mId;
	}
	
}
