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
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import jakarta.xml.bind.JAXBException;

import org.apache.commons.cli.AlreadySelectedException;
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
import de.uni_freiburg.informatik.ultimate.core.model.preferences.KeyValueUtil;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

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
		final List<Option> availableOptions = Arrays.asList(mCli.getOptions());

		final Set<String> optLongNames = new LinkedHashSet<>();
		for (final Option op : availableOptions) {

			final String opName = op.getLongOpt();

			// pluginId, settings label, preference item
			final Triple<String, String, UltimatePreferenceItem<?>> id2Label2Item =
					mOptionFactory.getUltimatePreference(opName);
			if (id2Label2Item == null) {
				continue;
			}

			final String id = id2Label2Item.getFirst();
			final String label = id2Label2Item.getSecond();
			final UltimatePreferenceItem<?> item = id2Label2Item.getThird();

			if (!optLongNames.add(op.getLongOpt())) {
				// we have already seen this Ultimate option. This is only allowed for KeyValue types.
				if (item.getType() != PreferenceType.KeyValue) {
					final String msg = String.format(
							"You already specified option %s for an option of type %s. Only options of type %s can be specified multiple times.",
							opName, item.getType(), PreferenceType.KeyValue);
					throw new AlreadySelectedException(msg);
				}
				// KeyValue types are retrieved with the first occurrence
				continue;
			}
			applyCliSetting(opName, services, id, label, item);
		}
	}

	private void applyCliSetting(final String optLongName, final IUltimateServiceProvider services, final String id,
			final String label, final UltimatePreferenceItem<?> item) throws ParseException {
		final IPreferenceProvider preferences = services.getPreferenceProvider(id);
		final String valueStr;
		if (item.getType() == PreferenceType.KeyValue) {
			final Object[] values = getParsedOptions(optLongName);
			valueStr = KeyValueUtil.toKeyValueString(values);
		} else {
			// note that this means that only KeyValue preferences can have duplicate occurrences. For all others, the
			// first occurrence counts and others are swallowed silently
			final Object value = getParsedOption(optLongName);
			valueStr = String.valueOf(value);
		}
		mLogger.info("Applying setting for plugin " + id + ": " + label + " -> " + valueStr);
		preferences.put(label, valueStr);

	}

	public boolean isHelpRequested() {
		return mCli.hasOption(CommandLineOptions.OPTION_NAME_HELP);
	}

	public boolean isVersionRequested() {
		return mCli.hasOption(CommandLineOptions.OPTION_LONG_NAME_VERSION);
	}

	public boolean isFrontendSettingsRequested() {
		return mCli.hasOption(CommandLineOptions.OPTION_LONG_NAME_FRONTEND_JSON_FROM_DEFAULTS);
	}

	public boolean isBackendWhitelistRequested() {
		return mCli.hasOption(CommandLineOptions.OPTION_LONG_NAME_BACKEND_WHITELIST_JSON_FROM_DEFAULTS);
	}

	public boolean isFrontendSettingsDeltaRequested() {
		return mCli.hasOption(CommandLineOptions.OPTION_LONG_NAME_FRONTEND_JSON_FROM_DELTA);
	}

	public boolean isBackendWhitelistDeltaRequested() {
		return mCli.hasOption(CommandLineOptions.OPTION_LONG_NAME_BACKEND_WHITELIST_JSON_FROM_DELTA);
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

		final List<File> files = new ArrayList<>(Arrays.asList(getInputFiles()));
		if (hasSettings()) {
			files.add(new File(getSettingsFile()));
		}
		files.add(getToolchainFile());
		final String joinednames = files.stream().map(File::getName).collect(Collectors.joining("_"));
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
	private <T> T[] getParsedOptions(final String optionName) throws ParseException {
		final Object[] obj = mCli.getParsedOptionValues(optionName);
		if (obj == null) {
			return null;
		}
		return (T[]) obj;
	}

	@SuppressWarnings("unchecked")
	private <T> T getParsedOption(final String optionName) throws ParseException {
		return (T) mCli.getParsedOptionValue(optionName);
	}

}
