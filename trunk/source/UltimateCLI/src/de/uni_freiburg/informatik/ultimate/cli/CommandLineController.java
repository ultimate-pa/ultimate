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
import java.util.Map.Entry;
import java.util.function.Predicate;

import org.apache.commons.cli.ParseException;
import org.eclipse.core.runtime.Platform;
import org.eclipse.equinox.app.IApplication;

import de.uni_freiburg.informatik.ultimate.cli.exceptions.InvalidFileException;
import de.uni_freiburg.informatik.ultimate.cli.options.CommandLineOptions;
import de.uni_freiburg.informatik.ultimate.cli.util.RcpUtils;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.BasicToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.DefaultToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultSummarizer;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.model.IController;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.ITool;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.Utils;

/**
 * The current command line controller for Ultimate provides a user interface for the command line.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class CommandLineController implements IController<RunDefinition> {

	private ILogger mLogger;
	private IToolchainData<RunDefinition> mToolchain;

	@Override
	public int init(final ICore<RunDefinition> core) {
		if (core == null) {
			return -1;
		}

		mLogger = core.getCoreLoggingService().getControllerLogger();

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Initializing CommandlineController...");
			mLogger.debug("Data directory is " + Platform.getLocation());
			mLogger.debug("Working directory is " + Platform.getInstallLocation().getURL());
			mLogger.debug("user.dir is " + System.getProperty("user.dir"));
			mLogger.debug("CLI Controller version is " + RcpUtils.getVersion(Activator.PLUGIN_ID));
		}

		final String[] args = Platform.getCommandLineArgs();

		// first, parse to see if toolchain is specified.
		final CommandLineParser toolchainStageParser = CommandLineParser.createCliOnlyParser(core);
		ParsedParameter toolchainStageParams;
		try {
			toolchainStageParams = toolchainStageParser.parse(args);

		} catch (final ParseException pex) {
			printParseException(args, toolchainStageParser, pex);
			return -1;
		}

		if (toolchainStageParams.isVersionRequested()) {
			mLogger.info("Version is " + RcpUtils.getVersion(Activator.PLUGIN_ID));
			mLogger.info(
					"Maximal heap size is " + Utils.humanReadableByteCount(Runtime.getRuntime().maxMemory(), true));
			return IApplication.EXIT_OK;
		}

		if (!toolchainStageParams.hasToolchain()) {
			if (toolchainStageParams.isHelpRequested()) {
				printHelp(toolchainStageParser, toolchainStageParams);
				return IApplication.EXIT_OK;
			}
			mLogger.info("Missing required option: " + CommandLineOptions.OPTION_NAME_TOOLCHAIN);
			printHelp(toolchainStageParser, toolchainStageParams);
			printAvailableToolchains(core);
			return IApplication.EXIT_OK;
		}

		final Predicate<String> pluginNameFilter;
		try {
			pluginNameFilter = getPluginFilter(core, toolchainStageParams.getToolchainFile());
		} catch (final ParseException pex) {
			mLogger.error("Could not find the provided toolchain file: " + pex.getMessage());
			return -1;
		}

		// second, perform real parsing
		final CommandLineParser fullParser = CommandLineParser.createCompleteParser(core, pluginNameFilter);
		final ParsedParameter fullParams;

		try {
			fullParams = fullParser.parse(args);
			if (fullParams.isHelpRequested()) {
				printHelp(fullParser, fullParams);
				return IApplication.EXIT_OK;
			}

			if (!fullParams.hasInputFiles()) {
				throw new ParseException("Missing required option: " + CommandLineOptions.OPTION_NAME_INPUTFILES);
			}

			if (fullParams.hasSettings()) {
				core.loadPreferences(fullParams.getSettingsFile());
			}

			mToolchain = fullParams.createToolchainData();

			fullParams.applyCliSettings(mToolchain.getServices());

			final File[] inputFiles = fullParams.getInputFiles();
			final BasicToolchainJob tcj =
					new DefaultToolchainJob("Processing Toolchain", core, this, mLogger, inputFiles);
			tcj.schedule();
			tcj.join();

		} catch (final ParseException pex) {
			printParseException(args, fullParser, pex);
			return -1;
		} catch (final InvalidFileException e) {
			mLogger.error("File in arguments violated specification: " + e.getMessage());
			return -1;
		} catch (@SuppressWarnings("squid:S2142") final InterruptedException e) {
			mLogger.fatal("Exception during execution of toolchain", e);
			return -1;
		}
		return IApplication.EXIT_OK;
	}

	private static void printHelp(final CommandLineParser toolchainStageParser,
			final ParsedParameter toolchainStageParams) {
		if (toolchainStageParams.showExperimentals()) {
			toolchainStageParser.printHelpWithExperimentals();
		} else {
			toolchainStageParser.printHelp();
		}
	}

	private void printParseException(final String[] args, final CommandLineParser toolchainStageParser,
			final ParseException pex) {
		mLogger.error(pex.getMessage());
		mLogger.error("Arguments were \"" + String.join(" ", args) + "\"");
		mLogger.error("--");
		toolchainStageParser.printHelp();
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
	public IToolchainData<RunDefinition> selectTools(final List<ITool> tools) {
		return mToolchain;
	}

	@Override
	public List<String> selectModel(final List<String> modelNames) {
		throw new UnsupportedOperationException("Interactively selecting models is not supported in CLI mode");
	}

	@Override
	public void displayToolchainResults(final IToolchainData<RunDefinition> toolchain,
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
	public void displayException(final IToolchainData<RunDefinition> toolchain, final String description,
			final Throwable ex) {
		mLogger.fatal("RESULT: An exception occured during the execution of Ultimate: " + description, ex);
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return null;
	}

	private Predicate<String> getPluginFilter(final ICore<RunDefinition> core, final File toolchainFileOrDir) {
		if (toolchainFileOrDir == null) {
			return a -> true;
		}
		final ToolchainLocator locator = new ToolchainLocator(toolchainFileOrDir, core, mLogger);
		return locator.createFilterForAvailableTools();
	}

	private void printAvailableToolchains(final ICore<RunDefinition> core) {
		final File workingDir = RcpUtils.getWorkingDirectory();
		final ToolchainLocator locator = new ToolchainLocator(workingDir, core, mLogger);

		final Map<File, IToolchainData<RunDefinition>> availableToolchains = locator.locateToolchains();
		if (availableToolchains.isEmpty()) {
			mLogger.warn("There are no toolchains in Ultimates working directory " + workingDir);
			return;
		}
		final String indent = "    ";

		mLogger.info("The following toolchains are available:");
		for (final Entry<File, IToolchainData<RunDefinition>> entry : availableToolchains.entrySet()) {
			mLogger.info(entry.getKey());
			mLogger.info(indent + entry.getValue().getToolchain().getName());
		}

	}

}
