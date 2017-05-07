package de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences;

import java.util.Collections;
import java.util.Map;

public class SpaceExPreferenceGroup extends PreferenceGroup {
	
	private final Map<String, String> mInitialLocations;
	
	public SpaceExPreferenceGroup(final Map<String, String> initialLocations, final String initialVariableInfix,
			final int id) {
		super(id, initialVariableInfix);
		mInitialLocations = (initialLocations != null) ? initialLocations : Collections.emptyMap();
	}
	
	public Map<String, String> getInitialLocations() {
		return mInitialLocations;
	}
	
	@Override
	public String toString() {
		return "{Locations: " + mInitialLocations + "\n Variables: " + mVariableInfix + "\n Id: " + mId + "}";
	}
	
}
