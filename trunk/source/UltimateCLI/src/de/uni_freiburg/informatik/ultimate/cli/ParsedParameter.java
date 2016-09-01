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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
import java.io.FileNotFoundException;
import java.util.Map;

import javax.xml.bind.JAXBException;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.ParseException;
import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ParsedParameter {

	private final Map<String, Pair<String, String>> mCliName2PreferenceName;
	private final CommandLine mCli;
	private final ICore<RunDefinition> mCore;
	private final ILogger mLogger;

	ParsedParameter(final ICore<RunDefinition> core, final CommandLine cli,
			final Map<String, Pair<String, String>> cliName2PreferenceName) {
		mCore = core;
		mCli = cli;
		mCliName2PreferenceName = cliName2PreferenceName;
		mLogger = core.getCoreLoggingService().getControllerLogger();
	}

	public void applyCliSettings(final IUltimateServiceProvider services) throws ParseException {
		for (final Option op : mCli.getOptions()) {
			applyCliSetting(op, services);
		}
	}

	private void applyCliSetting(final Option op, final IUltimateServiceProvider services) throws ParseException {
		final String optName = op.getLongOpt();
		final Pair<String, String> prefName = mCliName2PreferenceName.get(optName);
		if (prefName == null) {
			return;
		}
		final IPreferenceProvider preferences = services.getPreferenceProvider(prefName.getFirst());
		final String value = getParsedOption(optName);
		mLogger.info(
				"Applying setting for plugin " + prefName.getFirst() + ": " + prefName.getSecond() + " -> " + value);
		preferences.put(prefName.getSecond(), value);
	}

	public boolean isHelpRequested() {
		return mCli.hasOption(CommandLineOptions.OPTION_NAME_HELP);
	}

	public String getSettingsFile() throws ParseException, InvalidFileException {
		final File file = getParsedOption(CommandLineOptions.OPTION_NAME_SETTINGS);
		checkFileExists(file);
		return file.getAbsolutePath();
	}

	public boolean hasSettings() {
		return mCli.hasOption(CommandLineOptions.OPTION_NAME_SETTINGS);
	}

	public IToolchainData<RunDefinition> createToolchainData() throws InvalidFileException, ParseException {
		final File toolchainFile = getParsedOption(CommandLineOptions.OPTION_NAME_TOOLCHAIN);
		try {
			return mCore.createToolchainData(toolchainFile.getAbsolutePath());
		} catch (final FileNotFoundException e1) {
			throw new InvalidFileException(
					"Toolchain file not found at specified path: " + toolchainFile.getAbsolutePath());
		} catch (final JAXBException e1) {
			throw new InvalidFileException(
					"Toolchain file at path " + toolchainFile.getAbsolutePath() + " was malformed: " + e1.getMessage());
		} catch (final SAXException e1) {
			throw new InvalidFileException(
					"Toolchain file at path " + toolchainFile.getAbsolutePath() + " was malformed: " + e1.getMessage());
		}
	}

	public File[] getInputFiles() throws InvalidFileException, ParseException {
		final File[] inputFilesArgument = getInputFileArgument();
		if (inputFilesArgument == null || inputFilesArgument.length == 0) {
			throw new InvalidFileException("No input file specified");
		}

		for (final File file : inputFilesArgument) {
			checkFileExists(file);
		}
		return inputFilesArgument;
	}

	private File[] getInputFileArgument() {
		final String[] values = mCli.getOptionValues(CommandLineOptions.OPTION_NAME_INPUTFILES);
		final File[] files = new File[values.length];

		for (int i = 0; i < values.length; ++i) {
			files[i] = new File(values[i]);
		}

		return files;
	}

	private void checkFileExists(final File file) throws InvalidFileException {
		if (file == null || !file.exists()) {
			throw new InvalidFileException("File " + file.getAbsolutePath() + " does not exist");
		}
		if (!file.canRead()) {
			throw new InvalidFileException("Cannot read file " + file.getAbsolutePath());
		}
	}

	@SuppressWarnings("unchecked")
	private <T> T getParsedOption(final String optionName) throws ParseException {
		return (T) mCli.getParsedOptionValue(optionName);
	}
}
