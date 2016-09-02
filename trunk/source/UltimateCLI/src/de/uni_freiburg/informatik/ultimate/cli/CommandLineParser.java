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
import java.util.function.Predicate;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

import de.uni_freiburg.informatik.ultimate.cli.options.OptionBuilder;
import de.uni_freiburg.informatik.ultimate.cli.util.RcpUtils;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.lib.util.LoggerOutputStream;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class CommandLineParser {

	private final ILogger mLogger;
	private final Options mOptionsForParser;
	private final Options mOptionsForHelp;
	private final OptionBuilder mOptionBuilder;
	private final DefaultParser mParser;
	private final ICore<RunDefinition> mCore;
	private final ToolchainLocator mToolchainLocator;

	public CommandLineParser(final ICore<RunDefinition> core) {
		mCore = core;
		mLogger = core.getCoreLoggingService().getControllerLogger();
		mParser = new DefaultParser();
		mOptionBuilder = new OptionBuilder(core, mLogger);
		mToolchainLocator = new ToolchainLocator(RcpUtils.getWorkingDirectory(), core, mLogger);
		final Predicate<String> pluginNameFilter = mToolchainLocator.createFilterForAvailableTools();
		// final Predicate<String> pluginNameFilter = a -> true;
		mOptionsForParser = mOptionBuilder.getParserOptions(pluginNameFilter);
		mOptionsForHelp = mOptionBuilder.getHelpOptions(pluginNameFilter);

	}

	public void printHelp() {
		final HelpFormatter formatter = new HelpFormatter();
		final PrintWriter logPrintWriter = new PrintWriter(new LoggerOutputStream(mLogger::info));
		formatter.setLeftPadding(0);
		formatter.setDescPadding(6);
		formatter.setWidth(mOptionBuilder.getMaxOptionNameWidth() + 1);
		// keep the options in the order they were declared
		formatter.setOptionComparator(null);
		formatter.printHelp(logPrintWriter, "Ultimate [OPTIONS] -tc <FILE> -i <FILE> [<FILE> ...]", mOptionsForHelp);
		logPrintWriter.flush();
		logPrintWriter.close();
	}

	public ParsedParameter parse(final String[] args) throws ParseException {
		final CommandLine cli = mParser.parse(mOptionsForParser, args);
		validateParsedOptionsWithValidators(cli);
		validateParsedOptionsByConversion(cli);
		return new ParsedParameter(mCore, cli, mOptionBuilder);
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
			final IUltimatePreferenceItemValidator<Object> validator = mOptionBuilder.getValidator(cliName);
			if (validator == null) {
				continue;
			}
			final Object value = cli.getParsedOptionValue(cliName);
			if (!validator.isValid(value)) {
				throw new ParseException("Invalid option value for " + cliName + ": " + value);
			}
		}
	}

}
