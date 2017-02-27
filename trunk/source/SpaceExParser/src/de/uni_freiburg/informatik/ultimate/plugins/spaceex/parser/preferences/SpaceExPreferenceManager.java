/*
 * Copyright (C) 2016 Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE SpaceExParser plug-in.
 *
 * The ULTIMATE SpaceExParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SpaceExParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SpaceExParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SpaceExParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SpaceExParser plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences;

import java.io.File;
import java.io.FileInputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.HybridModel;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridSystem;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.util.SpaceExMathHelper;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Class that shall parse the config file of a SpaceEx model and hold important settings and values.
 *
 * @author Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 *
 */
public class SpaceExPreferenceManager {
	
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private String mSystem;
	private final String mModelFilename;
	// map that holds preferencegroups
	private final Map<Integer, SpaceExPreferenceGroup> mPreferenceGroups;
	private final Map<Integer, Map<String, String>> mGroupTodirectAssingment;
	// map of the form AUT -> VAR, necessary for Constants in config of the form AUT.VAR == 5
	private final Map<String, Map<String, String>> mRequiresRename;
	private final AtomicInteger mRenameID;
	// the forbiddengroups hold the specified locations + variables of the "forbidden" property.
	private final List<SpaceExForbiddenGroup> mForbiddenGroups;
	private final Map<String, List<String>> mForbiddenToForbiddenlocs;
	// Map that holds the parallel composition of each preference group.
	private Map<Integer, HybridAutomaton> mGroupIdToParallelComposition;
	private boolean mHasPreferenceGroups;
	private boolean mHasForbiddenGroup;
	private final SpaceExMathHelper mMathHelper;
	private SolverMode mSolverMode;
	private boolean mFakeNonIncrementalScript;
	private boolean mDumpSmtScriptToFile;
	private String mPathOfDumpedScript;
	private String mCommandExternalSolver;
	private boolean mDumpUsatCoreTrackBenchmark;
	private boolean mDumpMainTrackBenchmark;
	private String mLogicForExternalSolver;
	private Settings mSolverSettings;
	
	public SpaceExPreferenceManager(final IUltimateServiceProvider services, final ILogger logger,
			final File spaceExFile) throws Exception {
		mServices = services;
		mLogger = logger;
		final IPreferenceProvider preferenceProvider = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		mModelFilename = spaceExFile.getAbsolutePath();
		mPreferenceGroups = new HashMap<>();
		mGroupIdToParallelComposition = new HashMap<>();
		mForbiddenGroups = new ArrayList<>();
		mForbiddenToForbiddenlocs = new HashMap<>();
		mRequiresRename = new HashMap<>();
		mRenameID = new AtomicInteger(0);
		mMathHelper = new SpaceExMathHelper(logger);
		mGroupTodirectAssingment = new HashMap<>();
		// get TA settings
		getTraceAbstractionPreferences();
		String configfile =
				preferenceProvider.getString(SpaceExParserPreferenceInitializer.LABEL_SPACEEX_CONFIG_FILE).toString();
		final boolean loadconfig = preferenceProvider
				.getBoolean(SpaceExParserPreferenceInitializer.LABEL_LOAD_CONFIG_FILE_OF_SPACEEX_MODEL);
		// check if the configfile name is not empty
		// if it is search for a config file in the directory.
		if (!"".equals(configfile)) {
			final File config = new File(configfile);
			if (config.exists() && !config.isDirectory()) {
				parseConfigFile(config);
			}
		} else if (loadconfig) {
			configfile = spaceExFile.getAbsolutePath().replaceAll(".xml", ".cfg");
			final File config = new File(configfile);
			if (config.exists() && !config.isDirectory()) {
				parseConfigFile(config);
			} else {
				mLogger.info("no configfile with the name " + configfile + " exists");
			}
		}
	}
	
	// function that get the settings of the TraceAbstraction in order to create the correct solver.
	private void getTraceAbstractionPreferences() {
		final String taPluginID =
				de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator.PLUGIN_ID;
		final IPreferenceProvider traceAbstractionPreferences = mServices.getPreferenceProvider(taPluginID);
		mSolverMode = traceAbstractionPreferences.getEnum(RcfgPreferenceInitializer.LABEL_Solver, SolverMode.class);
		mFakeNonIncrementalScript = mServices.getPreferenceProvider(taPluginID)
				.getBoolean(RcfgPreferenceInitializer.LABEL_FakeNonIncrementalScript);
		
		mDumpSmtScriptToFile =
				mServices.getPreferenceProvider(taPluginID).getBoolean(RcfgPreferenceInitializer.LABEL_DumpToFile);
		mPathOfDumpedScript =
				mServices.getPreferenceProvider(taPluginID).getString(RcfgPreferenceInitializer.LABEL_Path);
		
		mCommandExternalSolver =
				mServices.getPreferenceProvider(taPluginID).getString(RcfgPreferenceInitializer.LABEL_ExtSolverCommand);
		
		mDumpUsatCoreTrackBenchmark = mServices.getPreferenceProvider(taPluginID)
				.getBoolean(RcfgPreferenceInitializer.LABEL_DumpUnsatCoreTrackBenchmark);
		
		mDumpMainTrackBenchmark = mServices.getPreferenceProvider(taPluginID)
				.getBoolean(RcfgPreferenceInitializer.LABEL_DumpMainTrackBenchmark);
		
		mLogicForExternalSolver =
				mServices.getPreferenceProvider(taPluginID).getString(RcfgPreferenceInitializer.LABEL_ExtSolverLogic);
		mSolverSettings = SolverBuilder.constructSolverSettings(mModelFilename, mSolverMode, mFakeNonIncrementalScript,
				mCommandExternalSolver, mDumpSmtScriptToFile, mPathOfDumpedScript);
		
	}
	
	private void parseConfigFile(final File configfile) throws Exception {
		mLogger.info("Parsing configfile: " + configfile);
		final long startTime = System.nanoTime();
		final Properties prop = new Properties();
		final FileInputStream fis = new FileInputStream(configfile);
		// load properties file
		prop.load(fis);
		// get properties
		// system holds the hybridsystem which is regarded.
		mSystem = prop.getProperty("system", "").replaceAll("\"", "");
		// initially holds the initial variable assignment, as well as initial locations.
		final String initially = prop.getProperty("initially", "").replaceAll("\"", "");
		final String forbidden = prop.getProperty("forbidden", "").replaceAll("\"", "");
		/*
		 * split "initially" into parts, split string at separator "&" initial location assignments are of the form:
		 * loc(#AUTOMATON NAME#)==#INITIAL LOCATION NAME# variable assignments are of the form: #VAR NAME#==#VALUE# OR
		 * #LOWER BOUND VALUE# <= #VARNAME# <= #UPPER BOUND VALUE#
		 */
		parseInitially(initially);
		parseForbidden(forbidden);
		fis.close();
		final long estimatedTime = System.nanoTime() - startTime;
		mLogger.info("Parsing configfile done in " + estimatedTime / (float) 1000000 + " milliseconds");
	}
	
	private void parseForbidden(final String forbidden) {
		if (!forbidden.isEmpty()) {
			final AtomicInteger id = new AtomicInteger(0);
			final List<String> formerGroups = mMathHelper.infixToGroups(forbidden);
			for (final String group : formerGroups) {
				mForbiddenGroups.add(createForbiddenGroup(group, id.incrementAndGet()));
			}
			mHasForbiddenGroup = true;
		} else {
			mLogger.info("-Config file has no forbidden property-");
			mHasForbiddenGroup = false;
		}
		
	}
	
	private void parseInitially(final String initially) {
		if (!initially.isEmpty()) {
			final AtomicInteger id = new AtomicInteger(0);
			final List<String> formerGroups = mMathHelper.infixToGroups(initially);
			// Parse the found groups and create Preference Groups.
			for (final String group : formerGroups) {
				final SpaceExPreferenceGroup preferenceGroup = createPreferenceGroup(group, id.incrementAndGet());
				mPreferenceGroups.put(preferenceGroup.getId(), preferenceGroup);
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Added new preference group: \n" + "Initial Locations:"
							+ preferenceGroup.getInitialLocations() + "\n" + "Initial variables: "
							+ preferenceGroup.getInitialVariableInfix());
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
	
	private SpaceExForbiddenGroup createForbiddenGroup(final String infix, final int id) {
		String initialVariableInfix = "";
		final Map<String, List<String>> initialLocations = new HashMap<>();
		// split at &
		final String[] splitted = infix.split("&");
		// for each initial statement, find out if it is variable or initial location definition.
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
				if (!initialLocations.containsKey(aut)) {
					final List<String> locList = new ArrayList<>();
					locList.add(loc);
					initialLocations.put(aut, locList);
				} else {
					initialLocations.get(aut).add(loc);
				}
			} else if (varMatcher.matches()) {
				String varString = varMatcher.group(0);
				final List<Pair<String, String>> renameList = analyseVariable(varMatcher.group(0));
				for (final Pair<String, String> pair : renameList) {
					mLogger.info(pair.getFirst());
					mLogger.info(pair.getSecond());
					varString = varString.replaceAll(pair.getFirst(), pair.getSecond());
				}
				mLogger.info(varString);
				initialVariableInfix += varString + "&";
			}
		}
		if (!initialVariableInfix.isEmpty()) {
			initialVariableInfix = initialVariableInfix.substring(0, initialVariableInfix.length() - 1);
		}
		final int groupid = id;
		return new SpaceExForbiddenGroup(initialLocations, initialVariableInfix, groupid);
	}
	
	private SpaceExPreferenceGroup createPreferenceGroup(final String infix, final int id) {
		String initialVariableInfix = "";
		final Map<String, String> initialLocations = new HashMap<>();
		// split at &
		final String[] splitted = infix.split("&");
		// for each initial statement, find out if it is variable or initial location definition.
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
				initialLocations.put(aut, loc);
			} else if (varMatcher.matches()) {
				String varString = varMatcher.group(0);
				final List<Pair<String, String>> renameList = analyseVariable(varMatcher.group(0));
				for (final Pair<String, String> pair : renameList) {
					varString = varString.replaceAll(pair.getFirst(), pair.getSecond());
				}
				saveDirectAssignments(varString, id);
				initialVariableInfix += varString + "&";
			}
		}
		if (!initialVariableInfix.isEmpty()) {
			initialVariableInfix = initialVariableInfix.substring(0, initialVariableInfix.length() - 1);
		}
		final int groupid = id;
		return new SpaceExPreferenceGroup(initialLocations, initialVariableInfix, groupid);
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
	 * Function that analyses if a variable in the config has to be renamed variables that have to be renamed are of the
	 * form AUT.VARNAME They are constants
	 *
	 * @param group
	 * @return
	 */
	private List<Pair<String, String>> analyseVariable(final String group) {
		final List<String> arr = SpaceExMathHelper.expressionToArray(group);
		final Pattern pattern = Pattern.compile("([a-z,A-Z]+)\\.([a-z,A-Z]+)");
		Matcher renameMatcher;
		final List<Pair<String, String>> renameList = new ArrayList<>();
		for (final String el : arr) {
			renameMatcher = pattern.matcher(el);
			if (renameMatcher.matches()) {
				final String aut = renameMatcher.group(1).replaceAll("_+.*", "");
				final String var = renameMatcher.group(2);
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
				renameList.add(new Pair<>(renameMatcher.group(0), newName));
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("##### HAS TO BE RENAMED: " + el + " #####");
					mLogger.debug("AUT: " + aut);
					mLogger.debug("VAR: " + var);
					mLogger.debug("NEW NAME: " + var);
					mLogger.debug("#########################################");
				}
			}
		}
		return renameList;
	}
	
	private String generateNewName(final String var) {
		return var + "_Renamedconst" + mRenameID.getAndIncrement();
	}
	
	public HybridSystem getRegardedSystem(final HybridModel model) {
		final String configSystem = mSystem != null ? mSystem : "";
		final Map<String, HybridSystem> systems = model.getSystems();
		// if the config file does not specify a system, get the first system of the model.
		if (configSystem.isEmpty()) {
			if (!systems.isEmpty()) {
				return systems.values().iterator().next();
			} else {
				throw new IllegalStateException("Hybridmodel" + model.toString() + " has no systems");
			}
		} else {
			// if the system specified in the config file is present in the models systems, get it
			if (systems.containsKey(configSystem)) {
				return systems.get(configSystem);
			} else if (systems.containsKey("system")) {
				return systems.get("system");
			} else {
				
				throw new UnsupportedOperationException("the system specified in the config file: \"" + configSystem
						+ "\" is not part of the hybrid model parsed from file: " + mModelFilename);
			}
		}
	}
	
	public String getSystem() {
		return mSystem;
	}
	
	public String getFileName() {
		return mModelFilename;
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
	
	public Map<Integer, HybridAutomaton> getGroupIdToParallelComposition() {
		return mGroupIdToParallelComposition;
	}
	
	public void setGroupIdToParallelComposition(final Map<Integer, HybridAutomaton> mGroupIdToParallelComposition) {
		this.mGroupIdToParallelComposition = mGroupIdToParallelComposition;
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
	
	public Map<String, List<String>> getForbiddenToForbiddenlocs() {
		return mForbiddenToForbiddenlocs;
	}
	
	public Map<Integer, Map<String, String>> getGroupTodirectAssingment() {
		return mGroupTodirectAssingment;
	}
	
	public SolverMode getSolverMode() {
		return mSolverMode;
	}
	
	public boolean ismFakeNonIncrementalScript() {
		return mFakeNonIncrementalScript;
	}
	
	public boolean ismDumpSmtScriptToFile() {
		return mDumpSmtScriptToFile;
	}
	
	public String getmPathOfDumpedScript() {
		return mPathOfDumpedScript;
	}
	
	public String getmCommandExternalSolver() {
		return mCommandExternalSolver;
	}
	
	public boolean ismDumpUsatCoreTrackBenchmark() {
		return mDumpUsatCoreTrackBenchmark;
	}
	
	public boolean ismDumpMainTrackBenchmark() {
		return mDumpMainTrackBenchmark;
	}
	
	public String getmLogicForExternalSolver() {
		return mLogicForExternalSolver;
	}
	
	public Settings getmSolverSettings() {
		return mSolverSettings;
	}
	
}
