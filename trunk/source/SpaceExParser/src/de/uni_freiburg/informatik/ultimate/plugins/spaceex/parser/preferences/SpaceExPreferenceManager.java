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
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.HybridModel;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridSystem;
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
	private final Map<String, String> mInitialLocations;
	private final Map<String, List<SignValuePair>> mInitialVariables;
	private String mInitialVariableInfix = "";
	
	public SpaceExPreferenceManager(IUltimateServiceProvider services, ILogger logger, File spaceExFile)
			throws Exception {
		mServices = services;
		mLogger = logger;
		final IPreferenceProvider preferenceProvider = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		String configfile =
				preferenceProvider.getString(SpaceExParserPreferenceInitializer.LABEL_SPACEEX_CONFIG_FILE).toString();
		final boolean loadconfig = preferenceProvider
				.getBoolean(SpaceExParserPreferenceInitializer.LABEL_LOAD_CONFIG_FILE_OF_SPACEEX_MODEL);
		mModelFilename = spaceExFile.getAbsolutePath();
		mInitialVariables = new HashMap<>();
		mInitialLocations = new HashMap<>();
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
	
	private void parseConfigFile(File configfile) throws Exception {
		mLogger.info("Parsing configfile: " + configfile);
		final Properties prop = new Properties();
		final FileInputStream fis = new FileInputStream(configfile);
		// load properties file
		prop.load(fis);
		// get properties
		// system holds the hybridsystem which is regarded.
		mSystem = prop.getProperty("system").replaceAll("\"", "");
		// initially holds the initial variable assignment, as well as initial locations.
		final String initially = prop.getProperty("initially").replaceAll("\"", "");
		/*
		 * split "initially" into parts, split string at separator "&" initial location assignments are of the form:
		 * loc(#AUTOMATON NAME#)==#INITIAL LOCATION NAME# variable assignments are of the form: #VAR NAME#==#VALUE# OR
		 * #LOWER BOUND VALUE# <= #VARNAME# <= #UPPER BOUND VALUE#
		 */
		if (!"".equals(initially)) {
			// split at &
			final String[] splitted = initially.split("&");
			// for each initial statement, find out if it is variable or initial location definition.
			String property;
			// regex stuff for initial locations
			final String locRegex = "loc\\((.*)\\)==(.*)";
			final Pattern locPattern = Pattern.compile(locRegex);
			Matcher locMatcher;
			// regex stuff for variables of the form v1<=var<=v2
			final String varRegex = "(.*)(<=|<|>|>=)(.*)(<=|<|>|>=)(.*)";
			final Pattern varPattern = Pattern.compile(varRegex);
			Matcher varMatcher;
			// regex stuff for variables of the form v1<=v2
			final String varRegex2 = "(.*)(<=|>=|<|>|==)(.*)";
			final Pattern varPattern2 = Pattern.compile(varRegex2);
			Matcher varMatcher2;
			for (int i = 0; i < splitted.length; i++) {
				property = splitted[i].replaceAll("\\s+", "");
				locMatcher = locPattern.matcher(property);
				varMatcher = varPattern.matcher(property);
				varMatcher2 = varPattern2.matcher(property);
				if (locMatcher.matches()) {
					final String aut = locMatcher.group(1);
					final String loc = locMatcher.group(2);
					mInitialLocations.put(aut, loc);
				} else if (varMatcher.matches()) {
					final String value1 = varMatcher.group(1);
					final String sign1 = varMatcher.group(2);
					final String var = varMatcher.group(3);
					final String sign2 = varMatcher.group(4);
					final String value2 = varMatcher.group(5);
					final List<SignValuePair> svPairs = new ArrayList<>();
					svPairs.add(new SignValuePair(sign1, value1));
					svPairs.add(new SignValuePair(sign2, value2));
					mInitialVariables.put(var, svPairs);
					mInitialVariableInfix += varMatcher.group(0) + ((i == splitted.length - 1) ? "" : "&");
				} else if (varMatcher2.matches()) {
					final String var = varMatcher2.group(1);
					final String sign = varMatcher2.group(2);
					final String value = varMatcher2.group(3);
					final List<SignValuePair> svPairs = new ArrayList<>();
					svPairs.add(new SignValuePair(sign, value));
					mInitialVariables.put(var, svPairs);
					mInitialVariableInfix += varMatcher2.group(0) + ((i == splitted.length - 1) ? "" : "&");
				}
			}
			mLogger.info(mInitialVariableInfix);
		}
		fis.close();
	}
	
	public HybridAutomaton getRegardedAutomaton(HybridModel model) {
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
					final Collection<HybridAutomaton> autcol = systems.get(configSystem).getAutomata().values();
					final Iterator<HybridAutomaton> it = autcol.iterator();
					aut = it.hasNext() ? it.next() : null;
				}
			}
		} else {
			throw new UnsupportedOperationException("the system specified in the config file: \"" + configSystem
					+ "\" is not part of the hybrid model parsed from file: " + mModelFilename);
		}
		if (aut == null) {
			throw new IllegalStateException("HybridAutomaton aut has not been assigned and is null");
		} else {
			return aut;
		}
	}
	
	public String getSystem() {
		return mSystem;
	}
	
	public Map<String, String> getInitialLocations() {
		return mInitialLocations;
	}
	
	public Map<String, List<SignValuePair>> getInitialVariables() {
		return mInitialVariables;
	}
	
	public String getFileName() {
		return mModelFilename;
	}
	
	public String getInitialInfix() {
		return mInitialVariableInfix;
	}
	
}
