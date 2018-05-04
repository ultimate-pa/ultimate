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
import java.io.IOException;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import javax.xml.bind.JAXBException;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.ParseException;
import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.cli.exceptions.InvalidFileArgumentException;
import de.uni_freiburg.informatik.ultimate.cli.options.CommandLineOptions;
import de.uni_freiburg.informatik.ultimate.cli.options.OptionBuilder;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class ParsedParameter {

	private final CommandLine mCli;
	private final ICore<RunDefinition> mCore;
	private final ILogger mLogger;
	private final OptionBuilder mOptionFactory;
	private String mCsvPrefix;

	ParsedParameter(final ICore<RunDefinition> core, final CommandLine cli, final OptionBuilder optionFactory) {
		mCore = core;
		mCli = cli;
		mOptionFactory = optionFactory;
		mLogger = core.getCoreLoggingService().getControllerLogger();
	}

	public void applyCliSettings(final IUltimateServiceProvider services) throws ParseException {
		for (final Option op : mCli.getOptions()) {
			applyCliSetting(op, services);
		}
	}

	private void applyCliSetting(final Option op, final IUltimateServiceProvider services) throws ParseException {
		final String optName = op.getLongOpt();
		final Pair<String, String> prefName = mOptionFactory.getUltimatePreference(optName);
		if (prefName == null) {
			return;
		}
		final IPreferenceProvider preferences = services.getPreferenceProvider(prefName.getFirst());
		final Object value = getParsedOption(optName);
		mLogger.info(
				"Applying setting for plugin " + prefName.getFirst() + ": " + prefName.getSecond() + " -> " + value);
		preferences.put(prefName.getSecond(), String.valueOf(value));
	}

	public boolean isHelpRequested() {
		return mCli.hasOption(CommandLineOptions.OPTION_NAME_HELP);
	}

	public boolean isVersionRequested() {
		return mCli.hasOption(CommandLineOptions.OPTION_LONG_NAME_VERSION);
	}

	public boolean showExperimentals() {
		return mCli.hasOption(CommandLineOptions.OPTION_LONG_NAME_EXPERIMENTAL);
	}

	public String getSettingsFile() throws ParseException, InvalidFileArgumentException {
		final File file = getParsedOption(CommandLineOptions.OPTION_NAME_SETTINGS);
		checkFileReadable(file, CommandLineOptions.OPTION_LONG_NAME_SETTINGS);
		return file.getAbsolutePath();
	}

	public boolean hasSettings() {
		return mCli.hasOption(CommandLineOptions.OPTION_NAME_SETTINGS);
	}

	public boolean hasToolchain() {
		return mCli.hasOption(CommandLineOptions.OPTION_NAME_TOOLCHAIN);
	}

	public boolean hasInputFiles() {
		return mCli.hasOption(CommandLineOptions.OPTION_NAME_INPUTFILES);
	}

	public boolean generateCsvs() {
		return mCli.hasOption(CommandLineOptions.OPTION_LONG_NAME_GENERATE_CSV);
	}

	private boolean hasCsvDirectory() {
		return mCli.hasOption(CommandLineOptions.OPTION_LONG_NAME_CSV_DIR);
	}

	public String getCsvPrefix() throws ParseException, InvalidFileArgumentException {
		if (generateCsvs() && mCsvPrefix == null) {
			mCsvPrefix = generateCsvPrefix();
		}
		return mCsvPrefix;
	}

	public File getCsvDirectory() throws ParseException, InvalidFileArgumentException {
		final File file = getParsedOption(CommandLineOptions.OPTION_LONG_NAME_CSV_DIR);
		checkFileRW(file, CommandLineOptions.OPTION_LONG_NAME_CSV_DIR);
		return file;
	}

	public File getToolchainFile() throws ParseException, InvalidFileArgumentException {
		final File file = getParsedOption(CommandLineOptions.OPTION_NAME_TOOLCHAIN);
		checkFileReadable(file, CommandLineOptions.OPTION_LONG_NAME_TOOLCHAIN);
		return file;
	}

	public IToolchainData<RunDefinition> createToolchainData() throws InvalidFileArgumentException, ParseException {
		final File toolchainFile = getToolchainFile();
		try {
			return mCore.createToolchainData(toolchainFile.getAbsolutePath());
		} catch (final FileNotFoundException e1) {
			throw new InvalidFileArgumentException(
					"Toolchain file not found at specified path: " + toolchainFile.getAbsolutePath());
		} catch (final SAXException | JAXBException e1) {
			throw new InvalidFileArgumentException(
					"Toolchain file at path " + toolchainFile.getAbsolutePath() + " was malformed: " + e1.getMessage());
		}
	}

	public File[] getInputFiles() throws InvalidFileArgumentException, ParseException {
		final File[] inputFilesArgument;
		try {
			inputFilesArgument = getInputFileArgument();
		} catch (final IOException ex) {
			throw new InvalidFileArgumentException(ex.getMessage(), ex);
		}

		if (inputFilesArgument == null || inputFilesArgument.length == 0) {
			throw new InvalidFileArgumentException("No input file specified");
		}
		return inputFilesArgument;
	}

	private String generateCsvPrefix() throws ParseException, InvalidFileArgumentException {
		String dir;
		if (hasCsvDirectory()) {
			dir = getCsvDirectory().getAbsolutePath();
		} else {
			dir = new File(".").getAbsolutePath();
		}

		final List<File> files = new ArrayList<>();
		files.addAll(Arrays.asList(getInputFiles()));
		if (hasSettings()) {
			files.add(new File(getSettingsFile()));
		}
		files.add(getToolchainFile());
		final String joinednames = files.stream().map(a -> a.getName()).collect(Collectors.joining("_"));
		return Paths.get(dir, joinednames).toString();
	}

	private File[] getInputFileArgument() throws IOException {
		final String[] values = mCli.getOptionValues(CommandLineOptions.OPTION_NAME_INPUTFILES);
		final List<File> files = new ArrayList<>();

		for (int i = 0; i < values.length; ++i) {
			final String value = values[i];
			if (value.contains("*")) {
				final int first = value.indexOf("*");
				try (DirectoryStream<Path> dirStream =
						Files.newDirectoryStream(Paths.get(value.substring(0, first - 1)), value.substring(first))) {
					dirStream.forEach(path -> files.add(path.toFile()));
				}
			} else {
				files.add(new File(values[i]));
			}
		}

		return files.toArray(new File[files.size()]);
	}

	private static void checkFileReadable(final File file, final String argumentName)
			throws InvalidFileArgumentException {
		if (file == null) {
			throw new IllegalArgumentException("file");
		}
		if (!file.exists()) {
			throw new InvalidFileArgumentException("Argument of \"" + argumentName + "\" has invalid value \""
					+ file.getAbsolutePath() + "\": File/Dir does not exist");
		}
		if (!file.canRead()) {
			throw new InvalidFileArgumentException("Argument of \"" + argumentName + "\" has invalid value \""
					+ file.getAbsolutePath() + "\": File/Dir cannot be read");
		}
	}

	private static void checkFileRW(final File file, final String argumentName) throws InvalidFileArgumentException {
		checkFileReadable(file, argumentName);
		if (!file.canWrite()) {
			throw new InvalidFileArgumentException("Argument of \"" + argumentName + "\" has invalid value \""
					+ file.getAbsolutePath() + "\": File/Dir cannot be written");
		}

	}

	@SuppressWarnings("unchecked")
	private <T> T getParsedOption(final String optionName) throws ParseException {
		final Object obj = mCli.getParsedOptionValue(optionName);
		return (T) obj;
	}

}
