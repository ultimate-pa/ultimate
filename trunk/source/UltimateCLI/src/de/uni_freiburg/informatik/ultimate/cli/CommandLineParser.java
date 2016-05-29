/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Core.
 * 
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Core grant you additional permission 
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

	private final ICore<?> mCore;
	private final ILogger mLogger;
	private final Options mOptions;
	private final DefaultParser mParser;
	private final Map<String, Pair<String, String>> mCliName2PreferenceName;
	private final Map<String, IUltimatePreferenceItemValidator<?>> mCliName2Validator;

	private int mMaxWidth;

	public CommandLineParser(ICore<?> core) {
		mCore = core;
		mLogger = core.getCoreLoggingService().getControllerLogger();
		mParser = new DefaultParser();
		mMaxWidth = Integer.MIN_VALUE;
		mCliName2PreferenceName = new HashMap<>();
		mCliName2Validator = new HashMap<>();

		mOptions = createOptions();
	}

	public void printHelp() {
		final HelpFormatter formatter = new HelpFormatter();
		final PrintWriter logPrintWriter = new PrintWriter(new LoggerOutputStream(a -> mLogger.info(a)));

		formatter.setWidth(mMaxWidth + 1);
		formatter.printHelp(logPrintWriter, "Ultimate", mOptions);
		logPrintWriter.flush();
		logPrintWriter.close();
	}

	public CommandLine parse(String[] args) {
		try {
			final CommandLine cli = mParser.parse(mOptions, args);
			validateParsedOptions(cli);
			return cli;
		} catch (ParseException e) {
			mLogger.error("Could not parse command-line options from arguments " + String.join(",", args) + ": "
					+ e.getMessage());
			return null;
		}
	}

	private void validateParsedOptions(final CommandLine cli) throws ParseException {
		for (final Option option : cli.getOptions()) {
			final String cliName = option.getLongOpt();
			final IUltimatePreferenceItemValidator<Object> validator = (IUltimatePreferenceItemValidator<Object>) mCliName2Validator
					.get(cliName);
			if (validator == null) {
				continue;
			}
			final Object value = cli.getParsedOptionValue(cliName);
			if (!validator.isValid(value)) {
				throw new ParseException("Invalid option value for " + cliName + ": " + value);
			}
		}
	}

	private Options createOptions() {
		final Options op = new Options();

		// create preferences from loaded Ultimate plugins
		for (final IUltimatePlugin plugin : mCore.getRegisteredUltimatePlugins()) {
			final IPreferenceInitializer preferences = plugin.getPreferences();
			if (preferences == null) {
				continue;
			}
			addPreferences(op, preferences);
		}
		// add platform options
		op.addOption(Option.builder("product").hasArg().type(String.class).build());
		op.addOption(Option.builder().longOpt("console").type(Boolean.class).build());

		return op;
	}

	private void addPreferences(final Options op, final IPreferenceInitializer preferences) {
		final String pluginId = preferences.getPluginID();
		for (UltimatePreferenceItem<?> item : BaseUltimatePreferenceItem
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
		final String longName = convertLabelToLongName(pluginId, item.getLabel());
		final StringBuilder sb = new StringBuilder();

		if (item.getToolTip() != null) {
			sb.append(item.getToolTip());
			sb.append(" ");
		}
		final Object[] choices = item.getChoices();
		if (choices != null && choices.length > 0) {
			sb.append("Valid choices are ");
			for (final Object choice : choices) {
				sb.append("\"");
				sb.append(choice.toString());
				sb.append("\", ");
			}
			sb.delete(sb.length() - 2, sb.length());
		}

		final Builder builder;
		if (sb.length() > 0) {
			builder = Option.builder().longOpt(longName).desc(sb.toString());
		} else {
			builder = Option.builder().longOpt(longName);
		}

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
		case Label:
		case SubItemContainer:
			return null;
		default:
			throw new IllegalArgumentException("PreferenceItem type " + item.getType() + " is not supported yet");
		}
	}

	private String convertLabelToLongName(final String pluginId, final String label) {
		final int lastIdx = pluginId.lastIndexOf('.');
		final String prefix = lastIdx > 0 ? pluginId.substring(lastIdx + 1) : pluginId;
		final String unprocessedName = prefix + " " + label;
		final String processedName = unprocessedName.replace(' ', '.').replace('(', '.').replace(')', '.')
				.replaceAll(":", "").toLowerCase();
		if (mMaxWidth < processedName.length()) {
			mMaxWidth = processedName.length();
		}
		mCliName2PreferenceName.put(processedName, new Pair<>(pluginId, label));
		return processedName;
	}

}
