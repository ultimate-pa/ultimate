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

import java.io.FileInputStream;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

public class SpaceExPreferenceManager {
	
	private IUltimateServiceProvider mServices;
	private ILogger mLogger;
	private String mConfigFile;
	private boolean mLoadConfig;
	private Map<String, String> mProperties;
	
	public SpaceExPreferenceManager(IUltimateServiceProvider services, ILogger logger) throws Exception{
		mServices = services;
		mLogger = logger;
		IPreferenceProvider preferenceProvider = mServices.getPreferenceProvider(de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.Activator.PLUGIN_ID);
		mConfigFile = preferenceProvider.getString(SpaceExParserPreferenceInitializer.LABEL_SPACEEX_CONFIG_FILE).toString();
		mLoadConfig = preferenceProvider.getBoolean(SpaceExParserPreferenceInitializer.LABEL_LOAD_CONFIG_FILE_OF_SPACEEX_MODEL);
		mProperties = new HashMap<>();
		parseConfigFile();
	}
	
	public void parseConfigFile() throws Exception{
		Properties prop = new Properties();
		final FileInputStream fis = new FileInputStream(mConfigFile);
		// load properties file
		prop.load(fis);
		// get properties
		// system holds the hybridsystem which is regarded.
		mProperties.put("system", prop.getProperty("system"));
		// initially holds the initial variable assignment, as well as initial locations.
		mProperties.put("initially", prop.getProperty("initially"));
		/* TODO: split "initially" into parts
		* IF the string is empty: set default values
		* default values for initial locations shall be:
		* 1. the first location seen.
		* 2. variables shall be initialized with the invariant of the initial location.
		* ELSE:
		* split string at separator "&"
		* initial location assignments are of the form: loc(#AUTOMATON NAME#)==#INITIAL LOCATION NAME#
		* variable assignments are of the form: #VAR NAME#==#VALUE# OR  #LOWER BOUND VALUE# <= #VARNAME# <= #UPPER BOUND VALUE#	
		*/ 
		mLogger.info(prop.getProperty("system"));
		mLogger.info(prop.getProperty("initially"));
		fis.close();			
	}
	
}
