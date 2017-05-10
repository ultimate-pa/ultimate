package de.uni_freiburg.informatik.ultimate.servercontroller.util;

import java.io.File;
import java.util.ListIterator;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.GnuParser;
//import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.OptionBuilder;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

public class CommandLineArgs {
	public static String SETTINGS_OPTION = "S";
	public static String INPUT_OPTION = "I";
	public static String TOOLCHAIN_OPTION = "TC";
	public static String PORT_OPTION = "P";
	public static String LISTEN_TIMEOUT_OPTION = "TIMEOUT";
	final static int DEFAULT_PORT = 6789;
	final static int DEFAULT_TIMEOUT = 60;

	final File mToolchainDirPath;
	final File mInputDirPath;
	final File mSettingsFilePath;
	final int mPort;
	final int mTimeout;

	public File getToolchainDirPath() {
		return mToolchainDirPath;
	}

	public File getInputDirPath() {
		return mInputDirPath;
	}

	public File getSettingsFilePath() {
		return mSettingsFilePath;
	}

	public int getPort() {
		return mPort;
	}

	public int getTimeout() {
		return mTimeout;
	}

	private CommandLineArgs(String toolchainDir, String inputDir, String settingsDir, int port, int timeout) {
		this.mToolchainDirPath = validateDir(toolchainDir);
		this.mInputDirPath = validateDir(inputDir);
		this.mSettingsFilePath = validateDir(settingsDir);
		this.mPort = port;
		this.mTimeout = timeout;
	}

	private static File validateDir(final String dirName) {
		final File dir = new File(dirName);
		if (!dir.isDirectory())
			throw new IllegalArgumentException(String.format("%1$s is not a valid Directory.", dirName));
		return dir;
	}

	public static CommandLineArgs parse(String[] args) throws ParseException {
		// Alter Java ist eine dermaßen Verbose kacke, ich werde Wahnsinnig.
		// Dieser hauffen FUCK Code hier macht schon, dass ich mir am liebsten
		// die Augen ausstechen möchte.
		// Von dem Krempel im CLI Controller ganz zu schweigen! Wie können
		// Menschen mit diesem shit produktiv arbeiten?

		CommandLine commandLine;
		Option option_tc = Option.builder(TOOLCHAIN_OPTION).argName("tc").hasArg().required().build();
		Option option_input =
				Option.builder(INPUT_OPTION).argName("i").hasArgs().required().desc("Input Files").build();
		Option option_setting =
				Option.builder(SETTINGS_OPTION).argName("s").hasArg().required().desc("Setting Files").build();
		Option port_setting = Option.builder(PORT_OPTION).argName("p").hasArg().desc("The Port").build();
		Option option_timeout = Option.builder(LISTEN_TIMEOUT_OPTION).argName("timeout").hasArg()
				.desc("Timeout for listening for incoming connections in seconds").build();
		Options options = new Options();
		CommandLineParser parser = new MyOwnStupidFuckingParser();
		// CommandLineParser parser = new DefaultParser();

		options.addOption(option_tc);
		options.addOption(option_input);
		options.addOption(option_setting);
		options.addOption(port_setting);
		options.addOption(option_timeout);

		commandLine = parser.parse(options, args);

		int port = DEFAULT_PORT;
		if (commandLine.hasOption(PORT_OPTION)) {
			final String portString = commandLine.getOptionValue(PORT_OPTION);
			try {
				port = Integer.parseInt(portString);
			} catch (NumberFormatException e) {
				throw new ParseException("Invalid value: " + portString + " cannot be parsed as port");
			}
		}
		int timeout = DEFAULT_TIMEOUT;
		if (commandLine.hasOption(LISTEN_TIMEOUT_OPTION)) {
			final String timeoutString = commandLine.getOptionValue(LISTEN_TIMEOUT_OPTION);
			try {
				timeout = Integer.parseInt(timeoutString);
			} catch (NumberFormatException e) {
				throw new ParseException("Invalid value: " + timeoutString + " cannot be parsed as timeout");
			}
		}

		return new CommandLineArgs(commandLine.getOptionValue(TOOLCHAIN_OPTION),
				commandLine.getOptionValue(INPUT_OPTION), commandLine.getOptionValue(SETTINGS_OPTION), port, timeout);
	}

	private static class MyOwnStupidFuckingParser extends GnuParser {
		@Override
		protected void processOption(final String arg, final ListIterator iter) throws ParseException {
			if (getOptions().hasOption(arg)) {
				super.processOption(arg, iter);
			}
		}
	}

}
