/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE SmtParser plug-in.
 *
 * The ULTIMATE SmtParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SmtParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SmtParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SmtParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SmtParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.source.smtparser;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.parsing.HCGBuilderHelper;
import de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.parsing.HornClauseParserScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.parsing.HCGBuilderHelper.ConstructAndInitializeBackendSmtSolver;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Scriptor;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtInterpolLogProxyWrapper;

/**
 * @author Daniel Dietsch
 * @author Matthias Heizmann
 */
public class SmtParser implements ISource {
	protected String[] mFileTypes;
	protected ILogger mLogger;
	protected List<String> mFileNames;
	protected Unit mPreludeUnit;
	private IUltimateServiceProvider mServices;
	private IToolchainStorage mStorage;
	private IElement output;

	public SmtParser() {
		mFileTypes = new String[] { "smt2" };
		mFileNames = new ArrayList<String>();
	}

	@Override
	public String getPluginID() {
		return getClass().getPackage().getName();
	}

	@Override
	public void init() {
		mFileNames = new ArrayList<String>();
	}

	@Override
	public String getPluginName() {
		return "SmtParser";
	}

	public String[] getTokens() {
		return null;
	}

	@Override
	public IElement parseAST(final File[] files) throws IOException {
		throw new UnsupportedOperationException("processing several files is not yet implemented");
	}

	@Override
	public IElement parseAST(final File file) throws IOException {
		if (file.isDirectory()) {
			return parseAST(file.listFiles());
		} else {
			processFile(file);
			return output;
		}
	}

	@Override
	public boolean parseable(final File[] files) {
		for (final File f : files) {
			if (!parseable(f)) {
				return false;
			}
		}
		return true;
	}

	@Override
	public boolean parseable(final File file) {
		for (final String s : getFileTypes()) {
			if (file.getName().endsWith(s)) {
				return true;
			}
		}
		return false;
	}

	@Override
	public String[] getFileTypes() {
		return mFileTypes;
	}

	@Override
	public ModelType getOutputDefinition() {
		return new ModelType(Activator.PLUGIN_ID, ModelType.Type.OTHER, mFileNames);
	}

	@Override
	public void setPreludeFile(final File prelude) {
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return new PreferenceInitializer();
	}

	@Override
	public void setToolchainStorage(final IToolchainStorage storage) {
		mStorage = storage;
	}

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void finish() {
		
	}
	
	private void processFile(final File file) throws IOException {
		
		final boolean useExternalSolver = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(PreferenceInitializer.LABEL_UseExtSolver);
		final String commandExternalSolver = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getString(PreferenceInitializer.LABEL_ExtSolverCommand);
		
		final boolean writeCommandsToFile = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(PreferenceInitializer.LABEL_WriteToFile);
		final String filename =
				mServices.getPreferenceProvider(Activator.PLUGIN_ID).getString(PreferenceInitializer.LABEL_Filename);

		final boolean inHornSolverMode = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(PreferenceInitializer.LABEL_HornSolverMode);
		
		final LogProxy logProxy = new SmtInterpolLogProxyWrapper(mLogger);
		Script script;
		if (inHornSolverMode) {
			mLogger.info("Parsing .smt2 file as a set of Horn Clauses");
			final ConstructAndInitializeBackendSmtSolver caibss =
					new HCGBuilderHelper.ConstructAndInitializeBackendSmtSolver(mServices, mStorage, null);
			script = new HornClauseParserScript(caibss.getScript(), caibss.getLogicForExternalSolver(),
					caibss.getSolverSettings());
			output = ((HornClauseParserScript) script).getHornClauses();
		} else {
			if (useExternalSolver) {
				mLogger.info("Starting external SMT solver with command " + commandExternalSolver);
				script = new Scriptor(commandExternalSolver, mLogger, mServices, mStorage,
						"external solver of SMT parser plugin");
			} else {
				mLogger.info("Starting SMTInterpol");
				script = new SMTInterpol(logProxy);
			}

			if (writeCommandsToFile) {
				final String abs = new File(filename).getAbsolutePath();
				mLogger.info("Writing all SMT commands to " + abs);
				script = new LoggingScript(script, filename, true);
			}
		}

		mLogger.info("Executing SMT file " + file.getAbsolutePath());
		final OptionMap optionMap = new OptionMap(logProxy, true);
		final ParseEnvironment parseEnv = new ParseEnvironment(script, optionMap);
		try {
			parseEnv.parseScript(file.getAbsolutePath());
			mLogger.info("Succesfully executed SMT file " + file.getAbsolutePath());
		} catch (final SMTLIBException exc) {
			mLogger.info("Failed while executing SMT file " + file.getAbsolutePath());
			mLogger.info("SMTLIBException " + exc.getMessage());
			parseEnv.printError(exc.getMessage());
		} finally {
			script.exit();
		}
	}
}
