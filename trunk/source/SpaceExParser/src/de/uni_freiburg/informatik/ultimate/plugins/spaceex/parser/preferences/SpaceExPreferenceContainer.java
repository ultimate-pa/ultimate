package de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences;

import java.util.List;
import java.util.Map;

public class SpaceExPreferenceContainer {
	
	String mSystem;
	// map that holds preferencegroups
	private final Map<Integer, SpaceExPreferenceGroup> mPreferenceGroups;
	
	// the forbiddengroups hold the specified locations + variables of the "forbidden" property.
	private final List<SpaceExForbiddenGroup> mForbiddenGroups;
	
	// map that holds value assignments (used to replace constants later on)
	private final Map<String, Map<String, String>> mRequiresRename;
	
	// map that holds direct assigments
	private final Map<Integer, Map<String, String>> mGroupTodirectAssingment;
	
	// booleans
	private final boolean mHasPreferenceGroups;
	private final boolean mHasForbiddenGroups;
	
	public SpaceExPreferenceContainer(final String system, final Map<Integer, SpaceExPreferenceGroup> initiallyGroups,
			final List<SpaceExForbiddenGroup> forbiddenGroups, final Map<String, Map<String, String>> renameMap,
			final Map<Integer, Map<String, String>> directAssingments) {
		mSystem = system;
		mPreferenceGroups = initiallyGroups;
		mForbiddenGroups = forbiddenGroups;
		mRequiresRename = renameMap;
		mGroupTodirectAssingment = directAssingments;
		mHasPreferenceGroups = mPreferenceGroups.isEmpty() ? false : true;
		mHasForbiddenGroups = mForbiddenGroups.isEmpty() ? false : true;
	}
	
	/*
	 * Getter/Setter
	 */
	public String getSystemName() {
		return mSystem;
	}
	
	public Map<String, Map<String, String>> getRequiresRename() {
		return mRequiresRename;
	}
	
	public Map<Integer, SpaceExPreferenceGroup> getPreferenceGroups() {
		return mPreferenceGroups;
	}
	
	public boolean hasPreferenceGroups() {
		return mHasPreferenceGroups;
	}
	
	public List<SpaceExForbiddenGroup> getForbiddenGroups() {
		return mForbiddenGroups;
	}
	
	public boolean hasForbiddenGroups() {
		return mHasForbiddenGroups;
	}
	
	public boolean isLocationForbidden(final String autName, final String locName) {
		if (mHasForbiddenGroups) {
			for (final SpaceExForbiddenGroup group : mForbiddenGroups) {
				if (group.getLocations().containsKey(autName) && group.getLocations().get(autName).contains(locName)) {
					return true;
				}
			}
		}
		return false;
	}
	
	public Map<Integer, Map<String, String>> getGroupTodirectAssingment() {
		return mGroupTodirectAssingment;
		
	}
	
}
