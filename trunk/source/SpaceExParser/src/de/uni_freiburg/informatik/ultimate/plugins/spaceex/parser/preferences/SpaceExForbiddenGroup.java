package de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences;

import java.util.List;
import java.util.Map;

public class SpaceExForbiddenGroup {
	private final int mId;
	private final Map<String, List<String>> mLocations;
	private final String mVariableInfix;
	
	public SpaceExForbiddenGroup(Map<String, List<String>> Locations, String initialVariableInfix, int id) {
		mId = id;
		mLocations = Locations;
		mVariableInfix = initialVariableInfix;
	}
	
	public Map<String, List<String>> getLocations() {
		return mLocations;
	}
	
	public String getVariableInfix() {
		return mVariableInfix;
	}
	
	public int getId() {
		return mId;
	}
	
	@Override
	public String toString() {
		return "{Locations: " + mLocations + "\n Variables: " + mVariableInfix + "\n Id: " + mId + "}";
	}
}
