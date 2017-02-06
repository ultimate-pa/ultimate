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
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.HybridModel;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridSystem;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg.HybridTermBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.Activator;

/**
 * Class that shall parse the config file of a SpaceEx model.
 * 
 * @author Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 *
 */
public class SpaceExPreferenceManager {
	
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private String mSystem;
	private final String mModelFilename;
	// replacement map for groups
	private final Map<String, String> mReplacement;
	// map that holds preferencegroups
	private final Map<Integer, SpaceExPreferenceGroup> mPreferenceGroups;
	// the forbiddengroup holds the specified locations + variables of the "forbidden" property.
	private final List<SpaceExForbiddenGroup> mForbiddenGroups;
	private final Map<String, List<String>> mForbiddenToForbiddenlocs;
	private Map<Integer, HybridAutomaton> mGroupIdToParallelComposition;
	private boolean mHasPreferenceGroups;
	private boolean mHasForbiddenGroup;
	
	public SpaceExPreferenceManager(final IUltimateServiceProvider services, final ILogger logger,
			final File spaceExFile) throws Exception {
		mServices = services;
		mLogger = logger;
		final IPreferenceProvider preferenceProvider = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		String configfile =
				preferenceProvider.getString(SpaceExParserPreferenceInitializer.LABEL_SPACEEX_CONFIG_FILE).toString();
		final boolean loadconfig = preferenceProvider
				.getBoolean(SpaceExParserPreferenceInitializer.LABEL_LOAD_CONFIG_FILE_OF_SPACEEX_MODEL);
		mModelFilename = spaceExFile.getAbsolutePath();
		mReplacement = new HashMap<>();
		mPreferenceGroups = new HashMap<>();
		mGroupIdToParallelComposition = new HashMap<>();
		mForbiddenGroups = new ArrayList<>();
		mForbiddenToForbiddenlocs = new HashMap<>();
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
			final List<String> formerGroups = infixToGroups(forbidden);
			for (final String group : formerGroups) {
				mForbiddenGroups.add(createForbiddenGroup(group, id.incrementAndGet()));
			}
			mHasForbiddenGroup = true;
		} else {
			mLogger.info("-Config file has no forbidden property-");
			mHasForbiddenGroup = false;
		}
		
	}
	
	private List<String> infixToGroups(final String infix) {
		final String infixWithLiterals = replaceAllWithLiterals(infix);
		final String[] infixToArray = HybridTermBuilder.expressionToArray(infixWithLiterals);
		final List<String> postfix = HybridTermBuilder.postfix(infixToArray);
		final List<String> groups = postfixToGroups(postfix);
		return replaceLiterals(groups);
	}
	
	private void parseInitially(final String initially) {
		testPostFixToGroups();
		if (!initially.isEmpty()) {
			final AtomicInteger id = new AtomicInteger(0);
			final List<String> formerGroups = infixToGroups(initially);
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
			if (mPreferenceGroups.isEmpty()) {
				mHasPreferenceGroups = false;
			} else {
				mHasPreferenceGroups = true;
			}
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
				final String aut = locMatcher.group(1).replaceAll("(_.*)", "");
				final String loc = locMatcher.group(2);
				if (!initialLocations.containsKey(aut)) {
					final List<String> locList = new ArrayList<>();
					locList.add(loc);
					initialLocations.put(aut, locList);
				} else {
					initialLocations.get(aut).add(loc);
				}
			} else if (varMatcher.matches()) {
				initialVariableInfix += varMatcher.group(0) + "&";
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
				initialVariableInfix += varMatcher.group(0) + "&";
			}
		}
		if (!initialVariableInfix.isEmpty()) {
			initialVariableInfix = initialVariableInfix.substring(0, initialVariableInfix.length() - 1);
		}
		final int groupid = id;
		return new SpaceExPreferenceGroup(initialLocations, initialVariableInfix, groupid);
	}
	
	// function to replace literals with their saved values
	private List<String> replaceLiterals(final List<String> groups) {
		final List<String> res = new ArrayList<>();
		for (final String group : groups) {
			String replacement = group.replaceAll("\\s+", "");
			for (final Map.Entry<String, String> entry : mReplacement.entrySet()) {
				final String rep = entry.getKey();
				final String loc = entry.getValue();
				replacement = replacement.replaceAll(rep, loc);
			}
			res.add(replacement);
		}
		return res;
	}
	
	// helper function to replace all elements in a string of the form x==2 & loc(x)==wuargh, with single literals.
	// x==2 & loc(x)==wuargh & y<=4---> A0 & A1 & A2
	private String replaceAllWithLiterals(final String initially) {
		// regex stuff for initial locations
		final String locRegex = "(.*)loc\\((.*)\\)==(.*)";
		final Pattern locPattern = Pattern.compile(locRegex);
		Matcher locMatcher;
		// regex stuff for variables of the form v1<=var<=v2 or x=v1.. etc
		final String varRegex = "(.*)(<=|<|>|>=)(.*)(<=|<|>|>=)(.*)|(.*)(<=|>=|<|>|==)(.*)";
		final Pattern varPattern = Pattern.compile(varRegex);
		Matcher varMatcher;
		String literal = "A";
		// replace all terms by a Literal
		final String[] splitted = initially.replaceAll("\\s+", "").split("(\\&)|(\\|)|(?<!loc)(\\()|(?!\\)==)(\\))");
		for (int i = 0; i < splitted.length; i++) {
			final String el = splitted[i];
			locMatcher = locPattern.matcher(el);
			varMatcher = varPattern.matcher(el);
			if (locMatcher.matches()) {
				if (!mReplacement.containsValue(locMatcher.group(0))) {
					mReplacement.put(literal + i, locMatcher.group(0));
				}
			} else if (varMatcher.matches()) {
				if (!mReplacement.containsValue(varMatcher.group(0))) {
					mReplacement.put(literal + i, varMatcher.group(0));
				}
			}
			if (i % 5 == 0) {
				final char[] charArr = literal.toCharArray();
				charArr[0]++;
				literal = Character.toString(charArr[0]);
			}
		}
		String replacement = initially.replaceAll("\\s+", "");
		for (final Map.Entry<String, String> entry : mReplacement.entrySet()) {
			final String rep = entry.getKey();
			final String loc = entry.getValue();
			replacement = replacement.replaceAll(Pattern.quote(loc), rep);
		}
		return replacement;
	}
	
	/**
	 * Function to convert a given formula postfix back notation to groups, the DNF.
	 * 
	 * @param postfix
	 * @return
	 */
	public List<String> postfixToGroups(final List<String> postfix) {
		/*
		 * TODO: Explain how the hell this algorithm works
		 */
		final Deque<String> stack = new LinkedList<>();
		final List<String> openGroupstack = new ArrayList<>();
		final List<String> finishedGroups = new ArrayList<>();
		// If the postfix does not contain any "&", we can simply split on | and return.
		if (!postfix.contains("&")) {
			for (final String element : postfix) {
				if (!HybridTermBuilder.isOperator(element)) {
					finishedGroups.add(element);
				}
			}
			return finishedGroups;
		} else if (!postfix.contains("|")) {
			final String infix = toInfix(postfix);
			finishedGroups.add(infix);
			return finishedGroups;
		}
		// Else we iterate over the postfix.
		for (final String element : postfix) {
			if (HybridTermBuilder.isOperator(element)) {
				final String operand1 = (!stack.isEmpty()) ? stack.pop() : "";
				final String operand2 = (!stack.isEmpty()) ? stack.pop() : "";
				/*
				 * Cases: - two single operands - & is operator and no groups exists yet --> initialize groups - & is
				 * operator and groups exist -> update groups - | is operator and groups exists -> add to finished
				 * groups - | is operator and no groups exists --> add to finished groups
				 */
				if (mReplacement.containsKey(operand1)
						&& (mReplacement.containsKey(operand2) || !operand2.contains("&")) && !operand2.isEmpty()) {
					// push Two single operands to stack
					stack.push(operand2 + element + operand1);
				} else if ("&".equals(element) && openGroupstack.isEmpty()) {
					// "initialization" of the different groups
					final List<String> eval = evaluateOperands(operand1, operand2);
					openGroupstack.addAll(eval);
				} else if ("&".equals(element) && !openGroupstack.isEmpty()) {
					// after the first time, operand 2 will never contain a & again.
					final List<String> removeList = new ArrayList<>();
					final List<String> newGroups = new ArrayList<>();
					// update groups
					for (final String group : openGroupstack) {
						if (operand1.contains("|")) {
							final List<String> eval = evaluateOrAndAnd(operand1, group);
							newGroups.addAll(eval);
						} else {
							final String newTerm = group + "&" + operand1;
							newGroups.add(newTerm);
						}
						removeList.add(group);
					}
					// remove old stuff
					for (final String group : removeList) {
						openGroupstack.remove(group);
					}
					openGroupstack.addAll(newGroups);
				} else if ("|".equals(element)) {
					if (openGroupstack.isEmpty() && !operand2.contains("&") && !operand1.contains("&")) {
						stack.push(operand2 + element + operand1);
					} else {
						if (!operand1.isEmpty()) {
							finishedGroups.add(operand1);
						}
						if (!operand2.isEmpty()) {
							finishedGroups.add(operand2);
						}
					}
				}
			} else {
				stack.push(element);
			}
		}
		if (!stack.isEmpty() && !stack.peek().contains("&")) {
			final String[] groups = stack.pop().replaceAll("(\\()|(\\))", "").split("\\|");
			for (final String group : groups) {
				openGroupstack.add(group);
			}
		}
		finishedGroups.addAll(openGroupstack);
		return finishedGroups;
		
	}
	
	private String toInfix(final List<String> postfix) {
		final Deque<String> stack = new LinkedList<>();
		// Else we iterate over the postfix.
		for (final String element : postfix) {
			if (HybridTermBuilder.isOperator(element)) {
				final String operand1 = stack.pop();
				final String operand2 = stack.pop();
				stack.push(operand2 + element + operand1);
			} else {
				stack.push(element);
			}
		}
		return stack.pop();
	}
	
	// function that evaluates operands and sets up the different groups
	private List<String> evaluateOperands(final String operand1, final String operand2) {
		final List<String> openGroupstack = new ArrayList<>();
		if (operand1.contains("|") && operand2.contains("|")) {
			final List<String> eval = evaluateOrAndOr(operand1, operand2);
			openGroupstack.addAll(eval);
		} else if (operand1.contains("|")) {
			final List<String> eval = evaluateOrAndAnd(operand1, operand2);
			openGroupstack.addAll(eval);
			
		} else if (operand2.contains("|")) {
			final List<String> eval = evaluateOrAndAnd(operand2, operand1);
			openGroupstack.addAll(eval);
			
		} else if (operand1.contains("&") && operand2.contains("&")) {
			openGroupstack.add(operand2 + "&" + operand1);
		}
		return openGroupstack;
	}
	
	private List<String> evaluateOrAndOr(final String operand1, final String operand2) {
		final List<String> res = new ArrayList<>();
		final String[] splitOP1 = operand1.replaceAll("(\\()|(\\))", "").split("(\\&)|(\\|)");
		final String[] splitOP2 = operand2.replaceAll("(\\()|(\\))", "").split("(\\&)|(\\|)");
		for (final String element : splitOP2) {
			for (final String element2 : splitOP1) {
				res.add(element2 + "&" + element);
			}
		}
		return res;
		
	}
	
	private List<String> evaluateOrAndAnd(final String operand1, final String operand2) {
		final List<String> res = new ArrayList<>();
		final String[] splitOP1 = operand1.replaceAll("(\\()|(\\))", "").split("(\\&)|(\\|)");
		for (final String el : splitOP1) {
			res.add(operand2 + "&" + el);
		}
		return res;
	}
	
	private void testPostFixToGroups() {
		final List<String> testStrings = new ArrayList<>();
		testStrings.add("A==1 & B==1 & (C==1 | D==1) & E==1");
		testStrings.add("A==1 & B==1 | C==1");
		testStrings.add("A==1");
		testStrings.add("A==1 | B==1");
		testStrings.add("A==1 & B==1");
		testStrings.add("A==1 & B==1 & (C==1 | D==1)");
		testStrings.add("A==1 & B==1 & (C==1 | D==1 | E==1)");
		testStrings.add("A==1 & B==1 & (C==1 | D==1) & E==1 | F==1");
		testStrings.add("A==1 & B==1 & (C==1 | D==1) & E==1 | F==1 & G==1");
		testStrings.add("A==1 & B==1 & (C==1 | D==1) & (E==1 | F==1) & G==1");
		
		for (final String testString : testStrings) {
			mLogger.info("########### START ###########");
			final String test = replaceAllWithLiterals(testString);
			mLogger.info(test);
			final String[] testarr = HybridTermBuilder.expressionToArray(test);
			final List<String> postfix = HybridTermBuilder.postfix(testarr);
			mLogger.info("postfix: " + postfix);
			final List<String> groups = postfixToGroups(postfix);
			mLogger.info("groups: " + groups);
			mLogger.info("########### END ###########");
		}
		
	}
	
	public HybridAutomaton getRegardedAutomaton(final HybridModel model) {
		/*
		 * in order to convert the hybrid model to an ICFG, we have to convert the parallelComposition of the regarded
		 * system.
		 */
		final String configSystem = mSystem != null ? mSystem : "";
		final Map<String, HybridSystem> systems = model.getSystems();
		final Map<String, HybridAutomaton> mergedAutomata = model.getMergedAutomata();
		HybridAutomaton aut;
		if (configSystem.isEmpty()) {
			if (!systems.isEmpty()) {
				final HybridSystem firstsys = systems.values().iterator().next();
				if (mergedAutomata.containsKey(firstsys.getName())) {
					aut = mergedAutomata.get(firstsys.getName());
				} else {
					aut = firstsys.getAutomata().values().iterator().next();
				}
			} else {
				throw new IllegalStateException("Hybridmodel" + model.toString() + " is empty");
			}
			return aut;
		}
		// if the system specified in the config file is present in the models systems
		if (systems.containsKey(configSystem)) {
			// if the system exists, we check if the system has a mergedAutomaton
			// if not it has to be a single automaton (at least it should be)
			if (mergedAutomata.containsKey(configSystem)) {
				aut = mergedAutomata.get(configSystem);
			} else {
				if (systems.get(configSystem).getAutomata().size() != 1) {
					throw new UnsupportedOperationException(
							"The automata of system" + systems.get(configSystem).getName()
									+ " have not been merged or are empty, the size of automata is:"
									+ systems.get(configSystem).getAutomata().size());
				} else {
					// should be a single automaton, thus just get it with an iterator.
					final HybridSystem firstsys = systems.values().iterator().next();
					if (mergedAutomata.containsKey(firstsys.getName())) {
						aut = mergedAutomata.get(firstsys.getName());
					} else {
						aut = firstsys.getAutomata().values().iterator().next();
					}
				}
			}
		} else {
			throw new UnsupportedOperationException("the system specified in the config file: \"" + configSystem
					+ "\" is not part of the hybrid model parsed from file: " + mModelFilename);
		}
		return aut;
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
	
	public void addToForbiddenlocs() {
		
	}
	
}
