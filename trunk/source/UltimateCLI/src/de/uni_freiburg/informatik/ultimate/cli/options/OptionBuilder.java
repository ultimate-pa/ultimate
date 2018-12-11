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
package de.uni_freiburg.informatik.ultimate.cli.options;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.function.Predicate;

import org.apache.commons.cli.Option;
import org.apache.commons.cli.Option.Builder;
import org.apache.commons.cli.Options;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.IUltimatePlugin;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class OptionBuilder {

	private static final int MAX_NAME_LENGTH = 160;
	private static final int MIN_WIDTH = 80;

	private final ICore<RunDefinition> mCore;
	private final Map<String, Triple<String, String, UltimatePreferenceItem<?>>> mCliName2UltimatePreferences;
	private final Map<String, IUltimatePreferenceItemValidator<?>> mCliName2Validator;
	private final ILogger mLogger;

	private final Options mUltimateOptions;
	private final Options mRcpOptions;
	private final Options mCliControllerOptions;

	public OptionBuilder(final ICore<RunDefinition> core, final ILogger logger, final boolean requireToolchain,
			final boolean requireInputFiles) {
		mCore = core;
		mCliName2UltimatePreferences = new HashMap<>();
		mCliName2Validator = new HashMap<>();
		mLogger = logger;

		mUltimateOptions = createUltimateOptions();
		mRcpOptions = createRcpOptions();
		mCliControllerOptions = createCliOptions(requireToolchain, requireInputFiles);
	}

	/**
	 * Given the long name of a CLI option, return a pair consisting of
	 *
	 * @param longOptName
	 * @return
	 */
	public Pair<String, String> getUltimatePreference(final String longOptName) {
		final Triple<String, String, UltimatePreferenceItem<?>> triple = mCliName2UltimatePreferences.get(longOptName);
		if (triple == null) {
			return null;
		}
		return new Pair<>(triple.getFirst(), triple.getSecond());
	}

	@SuppressWarnings("unchecked")
	public IUltimatePreferenceItemValidator<Object> getValidator(final String cliName) {
		return (IUltimatePreferenceItemValidator<Object>) mCliName2Validator.get(cliName);
	}

	public Options getParserOptions(final Predicate<String> pluginNameFilter) {
		final Options rtr = new Options();
		mCliControllerOptions.getOptions().stream().forEach(rtr::addOption);
		mUltimateOptions.getOptions().stream().filter(a -> filterUltimateOption(a, pluginNameFilter))
				.forEach(rtr::addOption);
		mRcpOptions.getOptions().stream().forEach(rtr::addOption);

		return rtr;
	}

	/**
	 * Return a {@link Options} instance containing only Ultimate options (no RCP options that should never be seen by
	 * the user).
	 *
	 * @param pluginNameFilter
	 *            A filter which can be used to remove Ultimate options from the set.
	 * @return A {@link Options} instance.
	 */
	public Options getHelpOptions(final Predicate<String> pluginNameFilter) {
		final Options rtr = new Options();

		mCliControllerOptions.getOptions().stream().forEach(rtr::addOption);
		mUltimateOptions.getOptions().stream().filter(a -> filterUltimateOption(a, pluginNameFilter))
				.forEach(rtr::addOption);

		return rtr;
	}

	public static int calculateMaxWidth(final Options opts) {
		if (opts == null) {
			return 0;
		}
		final Collection<Option> options = opts.getOptions();
		if (options.isEmpty()) {
			return 0;
		}
		final Optional<Integer> max = options.stream().map(a -> a.getLongOpt().length()).max(Integer::compare);
		// 8 is the length of the additional symbols for a long option line: --<option> <arg>
		if (!max.isPresent()) {
			throw new AssertionError("Java8 does not work");
		}
		final int calculatedMaxWidth = max.get() + 8;
		return calculatedMaxWidth > MIN_WIDTH ? calculatedMaxWidth : MIN_WIDTH;
	}

	public Options filterExperimentalOptions(final Options opts) {
		final Options rtr = new Options();
		opts.getOptions().stream().sequential().filter(a -> !isUltimateOptionWithoutDesc(a)).forEach(rtr::addOption);
		return rtr;
	}

	private boolean filterUltimateOption(final Option option, final Predicate<String> pluginNameFilter) {
		final Triple<String, String, UltimatePreferenceItem<?>> triple =
				mCliName2UltimatePreferences.get(option.getLongOpt());
		if (triple == null) {
			return false;
		}
		return pluginNameFilter.test(triple.getFirst());
	}

	private boolean isUltimateOptionWithoutDesc(final Option option) {
		final Triple<String, String, UltimatePreferenceItem<?>> triple =
				mCliName2UltimatePreferences.get(option.getLongOpt());
		if (triple == null) {
			return false;
		}
		final String desc = triple.getThird().getToolTip();
		return desc == null || desc.isEmpty();
	}

	private static Options createCliOptions(final boolean requireToolchain, final boolean requireInputFiles) {
		final Options op = new Options();

		// add CLI controller options
		for (final Option option : CommandLineOptions.createCliControllerOptions(requireToolchain, requireInputFiles)) {
			op.addOption(option);
		}

		return op;
	}

	private Options createUltimateOptions() {
		final Options op = new Options();

		// create options from preferences of loaded Ultimate plugins
		for (final IUltimatePlugin plugin : mCore.getRegisteredUltimatePlugins()) {
			final IPreferenceInitializer preferences = plugin.getPreferences();
			if (preferences == null) {
				continue;
			}

			addPreferences(op, preferences);
		}
		return op;
	}

	/**
	 * The options created here are only relevant for avoiding parse errors due to RCP parameters.
	 */
	private static Options createRcpOptions() {
		final Options op = new Options();
		// add platform options (they appear because of the way RCP launches and are never used by this controller)
		op.addOption(Option.builder("product").hasArg().type(String.class).build());
		op.addOption(Option.builder("application").hasArg().type(String.class).build());
		op.addOption(Option.builder().longOpt("console").type(Boolean.class).build());
		op.addOption(Option.builder().longOpt("launcher.suppressErrors").type(Boolean.class).build());
		op.addOption(
				Option.builder(CorePreferenceInitializer.RANDOM_WORKSPACE_CLI_OPTION_NAME).type(String.class).build());
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
			return builder.hasArg(true).numberOfArgs(1).type(Boolean.class).build();
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
		final String longName = convertLabelToLongName(pluginId, item);
		final String description = createDescription(item);

		final Builder builder;
		if (description.length() > 0) {
			builder = Option.builder().longOpt(longName).desc(description);
		} else {
			builder = Option.builder().longOpt(longName);
		}
		return builder;
	}

	private static String createDescription(final UltimatePreferenceItem<?> item) {
		final StringBuilder sb = new StringBuilder();

		if (item.getToolTip() != null) {
			sb.append(item.getToolTip());
			sb.append(" ");
		}

		switch (item.getType()) {
		case Boolean:
			sb.append("This option can either be true or false. ");
			break;
		case Color:
			sb.append("<arg> is a string representing a color. ");
			sb.append("The string has to be of the form \"red,green,blue\", where 0 <= red,green,blue <= 255. ");
			break;
		case Directory:
			sb.append(
					"<arg> is a string representing an absolute path to a single directory on the local file system. ");
			break;
		case File:
			sb.append("<arg> is a string representing an absolute path on the local file system to a single file. ");
			break;
		case Path:
			sb.append("<arg> is a string representing one or multiple paths to a file or directory on the system. ");
			sb.append("If multiple paths are specified by the user, they are separated by a semicolon. ");
			break;
		case Integer:
			sb.append("<arg> is a string representing an integer. ");
			break;
		case MultilineString:
		case String:
			sb.append("<arg> is a single line of text. ");
			break;
		case Radio:
		case Combo:
			sb.append("<arg> is a pre-defined value. ");
			break;
		case Label:
		case SubItemContainer:
			return sb.toString();
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
			sb.append(". ");
		}

		addDefaultValue(item, sb);

		return sb.toString();
	}

	private static void addDefaultValue(final UltimatePreferenceItem<?> item, final StringBuilder sb) {
		sb.append("The default value is " + item.getDefaultValue() + ". ");
	}

	/**
	 * This method converts the label of an {@link UltimatePreferenceItem} to a string that can be used on the command
	 * line.
	 */
	private String convertLabelToLongName(final String pluginId, final UltimatePreferenceItem<?> item) {
		final String label = item.getLabel();
		final int lastIdx = pluginId.lastIndexOf('.');
		final String prefix = lastIdx > 0 ? pluginId.substring(lastIdx + 1) : pluginId;
		final String unprocessedName = prefix + " " + label;
		final String processedName = unprocessedName.replace(' ', '.').replace('(', '.').replace(')', '.')
				.replaceAll(":", "").replace('"', '.').replace('\'', '.').replaceAll("\\.+", ".").toLowerCase();
		final int newLength = processedName.length();

		if (newLength > MAX_NAME_LENGTH) {
			mLogger.warn("Option " + processedName + " longer than allowed maximum of " + MAX_NAME_LENGTH);
		}

		mCliName2UltimatePreferences.put(processedName, new Triple<>(pluginId, label, item));
		return processedName;
	}

}
