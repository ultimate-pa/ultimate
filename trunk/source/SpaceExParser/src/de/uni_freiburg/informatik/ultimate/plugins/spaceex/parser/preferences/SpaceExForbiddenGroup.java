package de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class SpaceExForbiddenGroup {
	private final int mId;
	private final Map<String, List<String>> mLocations;
	private final String mVariableInfix;
	private final boolean mHasLocations;
	private final boolean mHasVariables;
	
	public SpaceExForbiddenGroup(final Map<String, List<String>> Locations, final String initialVariableInfix,
			final int id) {
		mId = id;
		mLocations = (!Locations.isEmpty()) ? Locations : new HashMap<>();
		mVariableInfix = initialVariableInfix;
		mHasLocations = (!Locations.isEmpty()) ? true : false;
		mHasVariables = (!initialVariableInfix.isEmpty()) ? true : false;
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
