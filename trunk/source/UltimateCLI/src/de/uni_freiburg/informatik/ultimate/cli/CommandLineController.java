/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE CLI plug-in.
 *
 * The ULTIMATE CLI plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CLI plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CLI plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CLI plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CLI plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cli;

import java.io.File;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import org.apache.commons.cli.ParseException;
import org.eclipse.core.runtime.Platform;
import org.eclipse.equinox.app.IApplication;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.BasicToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.DefaultToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultSummarizer;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.ToolchainListType;
import de.uni_freiburg.informatik.ultimate.core.model.IController;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.ITool;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * The current command line controller for Ultimate provides a user interface for the command line.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class CommandLineController implements IController<ToolchainListType> {

	private ILogger mLogger;
	private IToolchainData<ToolchainListType> mToolchain;

	@Override
	public int init(final ICore<ToolchainListType> core) {
		if (core == null) {
			return -1;
		}

		mLogger = core.getCoreLoggingService().getControllerLogger();
		mLogger.debug("Initializing CommandlineController...");

		final CommandLineParser newCmdParser = new CommandLineParser(core);
		final String[] args = Platform.getCommandLineArgs();
		try {
			final ParsedParameter pparams = newCmdParser.parse(args);
			if (pparams.isHelpRequested()) {
				newCmdParser.printHelp();
				return IApplication.EXIT_OK;
			}

			if (pparams.hasSettings()) {
				core.loadPreferences(pparams.getSettingsFile());
			}

			mToolchain = pparams.createToolchainData();

			pparams.applyCliSettings(mToolchain.getServices());

			final File[] inputFiles = pparams.getInputFiles();
			final BasicToolchainJob tcj =
					new DefaultToolchainJob("Processing Toolchain", core, this, mLogger, inputFiles);
			tcj.schedule();
			tcj.join();

		} catch (final ParseException e) {
			mLogger.error("Could not parse command-line options from arguments " + String.join(",", args) + ":");
			mLogger.error(e.getMessage());
			newCmdParser.printHelp();
			return -1;
		} catch (final InvalidFileException e) {
			mLogger.error("File in arguments violated specification: " + e.getMessage());
			return -1;
		} catch (final InterruptedException e) {
			mLogger.fatal("Exception during execution of toolchain", e);
			return -1;
		}
		return IApplication.EXIT_OK;
	}

	@Override
	public ISource selectParser(final Collection<ISource> parser) {
		throw new UnsupportedOperationException("Interactively selecting parsers is not supported in CLI mode");
	}

	@Override
	public String getPluginName() {
		return Activator.PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public IToolchainData<ToolchainListType> selectTools(final List<ITool> tools) {
		return mToolchain;
	}

	@Override
	public List<String> selectModel(final List<String> modelNames) {
		throw new UnsupportedOperationException("Interactively selecting models is not supported in CLI mode");
	}

	@Override
	public void displayToolchainResults(final IToolchainData<ToolchainListType> toolchain,
			final Map<String, List<IResult>> results) {
		final ResultSummarizer summarizer = new ResultSummarizer(results);
		switch (summarizer.getResultSummary()) {
		case CORRECT:
			mLogger.info("RESULT: Ultimate proved your program to be correct!");
			break;
		case INCORRECT:
			mLogger.info("RESULT: Ultimate proved your program to be incorrect!");
			break;
		default:
			mLogger.info("RESULT: Ultimate could not prove your program: " + summarizer.getResultDescription());
			break;
		}
	}

	@Override
	public void displayException(final IToolchainData<ToolchainListType> toolchain, final String description,
			final Throwable ex) {
		mLogger.fatal("RESULT: An exception occured during the execution of Ultimate: " + description, ex);
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return null;
	}

}
