package de.uni_freiburg.informatik.ultimate.servercontroller.util.cli;

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import java.util.ListIterator;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.GnuParser;
//import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

public final class CommandLineArgs {
	private final List<Option2<?, ?>> options = new ArrayList<>();
	public final IOption<File> Settings = new ExistingDirOption(
			Option.builder("S").argName("settings").hasArg().required().desc("Directory containing setting files"))
					.addTo(options);
	public final IOption<File> Toolchain = new ExistingDirOption(
			Option.builder("TC").argName("toolchain").hasArg().required().desc("Directory containing toolchain files"))
					.addTo(options);
	public final IOption<Boolean> ConfirmTC = new BoolOption(Option.builder("CONFIRMTC").argName("confirm").hasArg()
			.desc("Ask client for confirmation before starting toolchain.")).defaultValue(true).addTo(options);
	public final IOption<File> Input = new ExistingDirOption(
			Option.builder("I").argName("input").hasArg().required().desc("Directory containing input files"))
					.addTo(options);
	public final IOption<Integer> Port = new IntOption(Option.builder("P").argName("port").hasArg().desc("the port"))
			.defaultValue(6789).addTo(options);
	public final IOption<Integer> Timeout = new IntOption(Option.builder("TIMEOUT").argName("timeout").hasArg()
			.required().desc(("Timeout for listening for incoming connections in seconds"))).defaultValue(60)
					.addTo(options);

	private CommandLine getCommandline(final String[] arguments) throws ParseException {
		final Options cliOptions = new Options();
		options.forEach(o -> cliOptions.addOption(o.mOption));
		final CommandLineParser parser = new MyOwnStupidFuckingParser();
		return parser.parse(cliOptions, arguments);
	}

	private CommandLineArgs() {

	}

	public static CommandLineArgs parse(final String[] args) throws ParseException {
		final CommandLineArgs result = new CommandLineArgs();

		final CommandLine commandLine = result.getCommandline(args);

		for (final Option2<?, ?> option : result.options) {
			option.parse(commandLine);
		}

		return result;
	}

	private static class MyOwnStupidFuckingParser extends GnuParser {
		@Override
		protected void processOption(final String arg, final ListIterator iter) throws ParseException {
			if (getOptions().hasOption(arg)) {
				super.processOption(arg, iter);
			}
		}
	}

	public interface IOption<T> {
		T getValue();
	}
}
