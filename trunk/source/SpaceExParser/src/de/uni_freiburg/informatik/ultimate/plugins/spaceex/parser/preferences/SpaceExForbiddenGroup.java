package de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences;

import java.util.Collections;
import java.util.List;
import java.util.Map;

public class SpaceExForbiddenGroup extends PreferenceGroup {
	
	private final Map<String, List<String>> mLocations;
	private final boolean mHasLocations;
	private final boolean mHasVariables;
	
	public SpaceExForbiddenGroup(final Map<String, List<String>> locations, final String variableInfix, final int id) {
		super(id, variableInfix);
		mLocations = (!locations.isEmpty()) ? locations : Collections.emptyMap();
		mHasLocations = (!locations.isEmpty()) ? true : false;
		mHasVariables = (!variableInfix.isEmpty()) ? true : false;
	}
	
	public Map<String, List<String>> getLocations() {
		return mLocations;
	}
	
	public boolean hasLocations() {
		return mHasLocations;
	}
	
	public boolean hasVariables() {
		return mHasVariables;
	}
	
	@Override
	public String toString() {
		return "{Locations: " + mLocations + "\n Variables: " + mVariableInfix + "\n Id: " + mId + "}";
	}
}
