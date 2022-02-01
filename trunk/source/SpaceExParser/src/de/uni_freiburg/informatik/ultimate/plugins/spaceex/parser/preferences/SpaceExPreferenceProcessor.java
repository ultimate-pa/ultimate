package de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.util.SpaceExMathHelper;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class SpaceExPreferenceProcessor {
	
	private final ILogger mLogger;
	
	// map that holds preferencegroups
	private final Map<Integer, SpaceExPreferenceGroup> mPreferenceGroups;
	
	// the forbiddengroups hold the specified locations + variables of the "forbidden" property.
	private final List<SpaceExForbiddenGroup> mForbiddenGroups;
	
	// map that holds value assignments (used to replace constants later on)
	private final Map<String, Map<String, String>> mRequiresRename;
	private final AtomicInteger mRenameID;
	
	private boolean mHasPreferenceGroups;
	private boolean mHasForbiddenGroup;
	
	// group building variables
	// assume only one inital location per preference group.
	final Map<String, String> mInitialLocations;
	// assume that multiple locations may be forbidden.
	final Map<String, List<String>> mForbiddenLocations;
	
	private final Map<Integer, Map<String, String>> mGroupTodirectAssingment;
	
	private final SpaceExPreferenceContainer mProcessedPreferences;
	
	private enum GroupType {
		INITIALLY, FORBIDDEN
	}
	
	public SpaceExPreferenceProcessor(final ILogger logger, final String systemName, final String initially,
			final String forbidden) {
		mLogger = logger;
		mPreferenceGroups = new HashMap<>();
		mForbiddenGroups = new ArrayList<>();
		mRequiresRename = new HashMap<>();
		mRenameID = new AtomicInteger(0);
		mGroupTodirectAssingment = new HashMap<>();
		mInitialLocations = new HashMap<>();
		mForbiddenLocations = new HashMap<>();
		parseInitially(initially);
		parseForbidden(forbidden);
		mProcessedPreferences = new SpaceExPreferenceContainer(systemName, mPreferenceGroups, mForbiddenGroups,
				mRequiresRename, mGroupTodirectAssingment);
	}
	
	private void parseInitially(final String initially) {
		if (!initially.isEmpty()) {
			final AtomicInteger id = new AtomicInteger(0);
			final List<String> groups = SpaceExMathHelper.infixToGroups(initially);
			// Parse the found groups and create Preference Groups.
			for (final String group : groups) {
				final SpaceExPreferenceGroup preferenceGroup =
						(SpaceExPreferenceGroup) createGroup(group, id.incrementAndGet(), GroupType.INITIALLY);
				mPreferenceGroups.put(preferenceGroup.getId(), preferenceGroup);
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Added new preference group: \n" + "Initial Locations:"
							+ preferenceGroup.getInitialLocations() + "\n" + "Initial variables: "
							+ preferenceGroup.getVariableInfix());
				}
			}
		} else {
			mLogger.info("-Config file has no initially property-");
		}
		
		if (mPreferenceGroups.isEmpty()) {
			mHasPreferenceGroups = false;
		} else {
			mHasPreferenceGroups = true;
		}
	}
	
	private void parseForbidden(final String forbidden) {
		if (!forbidden.isEmpty()) {
			final AtomicInteger id = new AtomicInteger(0);
			final List<String> formerGroups = SpaceExMathHelper.infixToGroups(forbidden);
			for (final String group : formerGroups) {
				mForbiddenGroups
						.add((SpaceExForbiddenGroup) createGroup(group, id.incrementAndGet(), GroupType.FORBIDDEN));
			}
			mHasForbiddenGroup = true;
		} else {
			mLogger.info("-Config file has no forbidden property-");
			mHasForbiddenGroup = false;
		}
	}
	
	private PreferenceGroup createGroup(final String infix, final int id, final GroupType type) {
		// clear group building variables.
		mInitialLocations.clear();
		mForbiddenLocations.clear();
		
		final StringBuilder sb = new StringBuilder();
		// split infix at &
		final String[] splitted = infix.split("&");
		String property;
		// regex stuff for initial locations
		final String locRegex = "loc\\((.*)\\)==(.*)";
		final Pattern locPattern = Pattern.compile(locRegex);
		Matcher locMatcher;
		// regex stuff for variables of the form v1<=var<=v2 or x=v1.. etc
		final String varRegex = "(.*)(<=|<|>|>=)(.*)(<=|<|>|>=)(.*)|(.*)(<=|>=|<|>|==)(.*)";
		final Pattern varPattern = Pattern.compile(varRegex);
		Matcher varMatcher;
		for (final String element : splitted) {
			property = element.replaceAll("\\s+", "");
			locMatcher = locPattern.matcher(property);
			varMatcher = varPattern.matcher(property);
			if (locMatcher.matches()) {
				final String aut = locMatcher.group(1);
				final String loc = locMatcher.group(2);
				if (type == GroupType.INITIALLY) {
					mInitialLocations.put(aut, loc);
				} else if (type == GroupType.FORBIDDEN) {
					if (!mForbiddenLocations.containsKey(aut)) {
						final List<String> locList = new ArrayList<>();
						locList.add(loc);
						mForbiddenLocations.put(aut, locList);
					} else {
						mForbiddenLocations.get(aut).add(loc);
					}
				} else {
					throw new IllegalStateException("Type" + type + "is not supported");
				}
			} else if (varMatcher.matches()) {
				String varString = varMatcher.group(0);
				final List<Pair<String, String>> renameList = analyseVariable(varMatcher.group(0));
				for (final Pair<String, String> pair : renameList) {
					varString = varString.replaceAll(pair.getFirst(), pair.getSecond());
				}
				saveDirectAssignments(varString, id);
				sb.append(varString + "&");
			}
		}
		final String initialVariableInfix = sb.toString().substring(0, sb.toString().length() - 1);
		if (type == GroupType.INITIALLY) {
			return new SpaceExPreferenceGroup(mInitialLocations, initialVariableInfix, id);
		} else {
			return new SpaceExForbiddenGroup(mForbiddenLocations, initialVariableInfix, id);
		}
	}
	
	// save assingments of the form x==... as groupID -> (var -> val)
	private void saveDirectAssignments(final String varString, final int groupID) {
		final String[] splitted = varString.split("==");
		if (splitted.length == 2) {
			if (mGroupTodirectAssingment.containsKey(groupID)) {
				mGroupTodirectAssingment.get(groupID).put(splitted[0], splitted[1]);
			} else {
				final Map<String, String> varmap = new HashMap<>();
				varmap.put(splitted[0], splitted[1]);
				mGroupTodirectAssingment.put(groupID, varmap);
			}
		}
	}
	
	/**
	 * Function that analyses if a variable in the config has to be renamed. variables that have to be renamed are of
	 * the form SYSNAME.AUTNAME.VARNAME or similar.
	 *
	 * @param group
	 * @return
	 */
	private List<Pair<String, String>> analyseVariable(final String group) {
		final List<String> arr = SpaceExMathHelper.expressionToArray(group);
		final List<Pair<String, String>> renameList = new ArrayList<>();
		for (final String el : arr) {
			// matches for sys.aut.var and similar strings
			if (el.contains(".") && !el.matches("\\d*\\.?\\d+")) {
				// split into [sys.aut, var]
				// sys.aut defines to which system/automaton the variable belongs
				final String aut = el.substring(0, el.lastIndexOf('.'));
				final String var = el.substring(el.lastIndexOf('.') + 1, el.length());
				// generate a new name for the variable.
				String newName = generateNewName(var);
				if (mRequiresRename.containsKey(aut)) {
					if (!mRequiresRename.get(aut).containsKey(var)) {
						mRequiresRename.get(aut).put(var, newName);
					} else {
						newName = mRequiresRename.get(aut).get(var);
					}
				} else {
					final Map<String, String> map = new HashMap<>();
					map.put(var, newName);
					mRequiresRename.put(aut, map);
				}
				renameList.add(new Pair<>(el, newName));
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("##### HAS TO BE RENAMED: " + el + " #####");
					mLogger.debug("AUT: " + aut);
					mLogger.debug("VAR: " + var);
					mLogger.debug("NEW NAME: " + newName);
					mLogger.debug("#########################################");
				}
			}
		}
		return renameList;
	}
	
	private String generateNewName(final String var) {
		return var + "_Renamed" + mRenameID.getAndIncrement();
	}
	
	/*
	 * Getter/Setter
	 */
	
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
	
	public boolean hasForbiddenGroup() {
		return mHasForbiddenGroup;
	}
	
	public boolean isLocationForbidden(final String autName, final String locName) {
		if (mHasForbiddenGroup) {
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
	
	public SpaceExPreferenceContainer getProcessedPreferences() {
		return mProcessedPreferences;
	}
}
