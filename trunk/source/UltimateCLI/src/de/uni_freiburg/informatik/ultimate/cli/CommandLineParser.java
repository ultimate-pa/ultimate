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

import java.io.PrintWriter;
import java.util.HashMap;
import java.util.Map;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Option.Builder;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.ToolchainListType;
import de.uni_freiburg.informatik.ultimate.core.lib.util.LoggerOutputStream;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.IUltimatePlugin;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class CommandLineParser {

	private static final int MAX_NAME_LENGTH = 160;

	private final ICore<ToolchainListType> mCore;
	private final ILogger mLogger;
	private final Options mOptions;
	private final DefaultParser mParser;
	private final Map<String, Pair<String, String>> mCliName2PreferenceName;
	private final Map<String, IUltimatePreferenceItemValidator<?>> mCliName2Validator;

	private int mMaxOptionWidth;

	public CommandLineParser(final ICore<ToolchainListType> core) {
		mCore = core;
		mLogger = core.getCoreLoggingService().getControllerLogger();
		mParser = new DefaultParser();
		mMaxOptionWidth = Integer.MIN_VALUE;
		mCliName2PreferenceName = new HashMap<>();
		mCliName2Validator = new HashMap<>();

		mOptions = createOptions();
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Max width of options was " + mMaxOptionWidth);
		}
	}

	public void printHelp() {
		final HelpFormatter formatter = new HelpFormatter();
		final PrintWriter logPrintWriter = new PrintWriter(new LoggerOutputStream(mLogger::info));
		formatter.setLeftPadding(0);
		formatter.setDescPadding(6);
		formatter.setWidth(mMaxOptionWidth + 1);
		// keep the options in the order they were declared
		formatter.setOptionComparator(null);
		formatter.printHelp(logPrintWriter, "Ultimate [OPTIONS] -tc <FILE> -i <FILE> [<FILE> ...]", mOptions);
		logPrintWriter.flush();
		logPrintWriter.close();
	}

	public ParsedParameter parse(final String[] args) throws ParseException {
		final CommandLine cli = mParser.parse(mOptions, args);
		validateParsedOptionsWithValidators(cli);
		validateParsedOptionsByConversion(cli);
		return new ParsedParameter(mCore, cli, mCliName2PreferenceName);
	}

	private void validateParsedOptionsByConversion(final CommandLine cli) throws ParseException {
		for (final Option option : cli.getOptions()) {
			String optName = option.getOpt();
			if (optName == null) {
				optName = option.getLongOpt();
			}
			final Object parsedValue = cli.getParsedOptionValue(optName);
			if (mLogger.isDebugEnabled() && parsedValue != null) {
				mLogger.debug("Option " + optName + " has value of type " + parsedValue.getClass().getCanonicalName()
						+ ": " + parsedValue);
			}
		}
	}

	private void validateParsedOptionsWithValidators(final CommandLine cli) throws ParseException {
		for (final Option option : cli.getOptions()) {
			final String cliName = option.getLongOpt();
			if (cliName == null) {
				continue;
			}
			final IUltimatePreferenceItemValidator<Object> validator = getValidator(cliName);
			if (validator == null) {
				continue;
			}
			final Object value = cli.getParsedOptionValue(cliName);
			if (!validator.isValid(value)) {
				throw new ParseException("Invalid option value for " + cliName + ": " + value);
			}
		}
	}

	@SuppressWarnings("unchecked")
	private IUltimatePreferenceItemValidator<Object> getValidator(final String cliName) {
		return (IUltimatePreferenceItemValidator<Object>) mCliName2Validator.get(cliName);
	}

	private Options createOptions() {
		final Options op = new Options();

		// add CLI controller options
		for (final Option option : CommandLineOptions.createCommandLineOptions()) {
			op.addOption(option);
		}
		// create preferences from loaded Ultimate plugins
		for (final IUltimatePlugin plugin : mCore.getRegisteredUltimatePlugins()) {
			final IPreferenceInitializer preferences = plugin.getPreferences();
			if (preferences == null) {
				continue;
			}
			addPreferences(op, preferences);
		}

		// add platform options (they appear because of the way RCP launches and are never used by this controller)
		op.addOption(Option.builder("product").hasArg().type(String.class).build());
		op.addOption(Option.builder("application").hasArg().type(String.class).build());
		op.addOption(Option.builder().longOpt("console").type(Boolean.class).build());
		op.addOption(Option.builder().longOpt("launcher.suppressErrors").type(Boolean.class).build());

		return op;
	}

	private void addPreferences(final Options op, final IPreferenceInitializer preferences) {
		final String pluginId = preferences.getPluginID();
		for (final UltimatePreferenceItem<?> item : BaseUltimatePreferenceItem
				.constructFlattenedList(preferences.getPreferenceItems())) {
			final Option option = createOption(item, pluginId);
			if (option == null) {
				continue;
			}
			op.addOption(option);
			addValidator(option.getLongOpt(), item);
		}
	}

	private void addValidator(final String cliName, final UltimatePreferenceItem<?> item) {
		final IUltimatePreferenceItemValidator<?> validator = item.getPreferenceValidator();
		if (validator == null) {
			return;
		}
		mCliName2Validator.put(cliName, validator);
	}

	private Option createOption(final UltimatePreferenceItem<?> item, final String pluginId) {
		switch (item.getType()) {
		case Label:
		case SubItemContainer:
			return null;
		default:
			break;
		}

		final Builder builder = createBuilder(item, pluginId);

		switch (item.getType()) {
		case Boolean:
			return builder.hasArg(false).type(Boolean.class).build();
		case Integer:
			return builder.hasArg(true).numberOfArgs(1).type(Integer.class).build();
		case Combo:
		case Color:
		case Directory:
		case File:
		case MultilineString:
		case Path:
		case Radio:
		case String:
			return builder.hasArg(true).numberOfArgs(1).type(String.class).build();
		default:
			throw new IllegalArgumentException("PreferenceItem type " + item.getType() + " is not supported yet");
		}
	}

	private Builder createBuilder(final UltimatePreferenceItem<?> item, final String pluginId) {
		final String longName = convertLabelToLongName(pluginId, item.getLabel());
		final String description = createDescription(item);

		final Builder builder;
		if (description.length() > 0) {
			builder = Option.builder().longOpt(longName).desc(description);
		} else {
			builder = Option.builder().longOpt(longName);
		}
		return builder;
	}

	private String createDescription(final UltimatePreferenceItem<?> item) {
		final StringBuilder sb = new StringBuilder();

		if (item.getToolTip() != null) {
			sb.append(item.getToolTip());
			sb.append(" ");
		}

		switch (item.getType()) {
		case Boolean:
			sb.append("This option is a flag.");
			break;
		case Color:
			sb.append("<arg> is a string representing a color. ");
			sb.append("The string has to be of the form \"red,green,blue\", where 0 <= red,green,blue <= 255.");
			break;
		case Directory:
			sb.append("<arg> is a string representing an absolute path ");
			sb.append("to a single directory on the local file system.");
			break;
		case File:
			sb.append("<arg> is a string representing an absolute path on the local file system to a single file.");
			break;
		case Path:
			sb.append("<arg> is a string representing one or multiple paths to a file or directory on the system. ");
			sb.append("If multiple paths are specified by the user, they are separated by a semicolon.");
			break;
		case Integer:
			sb.append("<arg> is a string representing an integer.");
			break;
		case MultilineString:
		case String:
			sb.append("<arg> is a single line of text.");
			break;
		default:
			break;
		}

		final Object[] choices = item.getChoices();
		if (choices != null && choices.length > 0) {
			sb.append("Valid choices for <arg> are ");
			for (final Object choice : choices) {
				sb.append("\"");
				sb.append(choice.toString());
				sb.append("\", ");
			}
			sb.delete(sb.length() - 2, sb.length());
			sb.append(".");
		}
		return sb.toString();
	}

	private String convertLabelToLongName(final String pluginId, final String label) {
		final int lastIdx = pluginId.lastIndexOf('.');
		final String prefix = lastIdx > 0 ? pluginId.substring(lastIdx + 1) : pluginId;
		final String unprocessedName = prefix + " " + label;
		final String processedName = unprocessedName.replace(' ', '.').replace('(', '.').replace(')', '.')
				.replaceAll(":", "").replace('"', '.').replaceAll("\\.+", ".").toLowerCase();
		final int newLength = processedName.length();
		if (mMaxOptionWidth < newLength) {
			mMaxOptionWidth = newLength;
		}
		if (newLength > MAX_NAME_LENGTH) {
			mLogger.warn("Option " + processedName + " longer than allowed maximum of " + MAX_NAME_LENGTH);
		}

		mCliName2PreferenceName.put(processedName, new Pair<>(pluginId, label));
		return processedName;
	}

}
