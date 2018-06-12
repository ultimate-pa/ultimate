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
import java.util.Properties;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.util.HybridTranslatorConstants;

/**
 * Class that shall parse the config file of a SpaceEx model and hold important settings and values.
 *
 * @author Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 *
 */
public class SpaceExPreferenceManager {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final String mModelFilename;
	private String mSystem;
	private String mInitially;
	private String mForbidden;
	// Trace abstraction settings / SMT toolkit settings
	private SolverMode mSolverMode;
	private boolean mFakeNonIncrementalScript;
	private boolean mDumpSmtScriptToFile;
	private String mPathOfDumpedScript;
	private String mCommandExternalSolver;
	private boolean mDumpUsatCoreTrackBenchmark;
	private boolean mDumpMainTrackBenchmark;
	private String mLogicForExternalSolver;
	private SolverSettings mSolverSettings;

	public SpaceExPreferenceManager(final IUltimateServiceProvider services, final ILogger logger,
			final File spaceExFile) throws Exception {
		mServices = services;
		mLogger = logger;
		final IPreferenceProvider preferenceProvider = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		mModelFilename = spaceExFile.getName();
		// get TA settings
		getTraceAbstractionPreferences();
		String configfile =
				preferenceProvider.getString(SpaceExParserPreferenceInitializer.LABEL_SPACEEX_CONFIG_FILE).toString();
		final boolean loadconfig = preferenceProvider
				.getBoolean(SpaceExParserPreferenceInitializer.LABEL_LOAD_CONFIG_FILE_OF_SPACEEX_MODEL);
		// check if the configfile name is not empty
		// if it is search for a config file in the directory.
		if (!configfile.isEmpty()) {
			initializeConfigParsing(configfile);
		} else if (loadconfig) {
			configfile = spaceExFile.getAbsolutePath().replaceAll(".xml", ".cfg");
			initializeConfigParsing(configfile);
		}
	}

	private void initializeConfigParsing(final String configfile) throws Exception {
		final File config = new File(configfile);
		if (config.exists() && !config.isDirectory()) {
			parseConfigFile(config);
		} else {
			mLogger.info("no configfile with the name " + configfile + " exists");
		}

	}

	// function that get the settings of the TraceAbstraction in order to create the correct solver.
	private void getTraceAbstractionPreferences() {
		final String TRACE_ABSTRACTION_PLUGIN_ID =
				de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator.PLUGIN_ID;
		final IPreferenceProvider traceAbstractionPreferences =
				mServices.getPreferenceProvider(TRACE_ABSTRACTION_PLUGIN_ID);
		mSolverMode = traceAbstractionPreferences.getEnum(RcfgPreferenceInitializer.LABEL_SOLVER, SolverMode.class);
		mFakeNonIncrementalScript = mServices.getPreferenceProvider(TRACE_ABSTRACTION_PLUGIN_ID)
				.getBoolean(RcfgPreferenceInitializer.LABEL_FAKE_NON_INCREMENTAL_SCRIPT);

		mDumpSmtScriptToFile = mServices.getPreferenceProvider(TRACE_ABSTRACTION_PLUGIN_ID)
				.getBoolean(RcfgPreferenceInitializer.LABEL_DUMP_TO_FILE);
		mPathOfDumpedScript = mServices.getPreferenceProvider(TRACE_ABSTRACTION_PLUGIN_ID)
				.getString(RcfgPreferenceInitializer.LABEL_DUMP_PATH);

		mCommandExternalSolver = mServices.getPreferenceProvider(TRACE_ABSTRACTION_PLUGIN_ID)
				.getString(RcfgPreferenceInitializer.LABEL_EXT_SOLVER_COMMAND);

		mDumpUsatCoreTrackBenchmark = mServices.getPreferenceProvider(TRACE_ABSTRACTION_PLUGIN_ID)
				.getBoolean(RcfgPreferenceInitializer.LABEL_DUMP_UNSAT_CORE_BENCHMARK);

		mDumpMainTrackBenchmark = mServices.getPreferenceProvider(TRACE_ABSTRACTION_PLUGIN_ID)
				.getBoolean(RcfgPreferenceInitializer.LABEL_DUMP_MAIN_TRACK_BENCHMARK);

		mLogicForExternalSolver = mServices.getPreferenceProvider(TRACE_ABSTRACTION_PLUGIN_ID)
				.getString(RcfgPreferenceInitializer.LABEL_EXT_SOLVER_LOGIC);
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
		mSystem = prop.getProperty(HybridTranslatorConstants.CONFIG_SYSTEM_PROPERTY, "").replaceAll("\"", "");
		// initially holds the initial variable assignment, as well as initial locations.
		mInitially = prop.getProperty(HybridTranslatorConstants.CONFIG_INITIALLY_PROPERTY, "").replaceAll("\"", "");
		mForbidden = prop.getProperty(HybridTranslatorConstants.CONFIG_FORBIDDEN_PROPERTY, "").replaceAll("\"", "");
		fis.close();
		final long estimatedTime = System.nanoTime() - startTime;
		mLogger.info("Parsing configfile done in " + estimatedTime / (float) 1000000 + " milliseconds");
	}

	public String getSystem() {
		return mSystem;
	}

	public SolverMode getSolverMode() {
		return mSolverMode;
	}

	public boolean isFakeNonIncrementalScript() {
		return mFakeNonIncrementalScript;
	}

	public boolean isDumpSmtScriptToFile() {
		return mDumpSmtScriptToFile;
	}

	public String getPathOfDumpedScript() {
		return mPathOfDumpedScript;
	}

	public String getCommandExternalSolver() {
		return mCommandExternalSolver;
	}

	public boolean isDumpUsatCoreTrackBenchmark() {
		return mDumpUsatCoreTrackBenchmark;
	}

	public boolean isDumpMainTrackBenchmark() {
		return mDumpMainTrackBenchmark;
	}

	public String getLogicForExternalSolver() {
		return mLogicForExternalSolver;
	}

	public SolverSettings getSolverSettings() {
		return mSolverSettings;
	}

	public String getInitially() {
		return mInitially;
	}

	public String getForbidden() {
		return mForbidden;
	}

}
