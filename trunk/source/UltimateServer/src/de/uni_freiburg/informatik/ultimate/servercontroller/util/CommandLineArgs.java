package de.uni_freiburg.informatik.ultimate.servercontroller.util;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.GnuParser;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.OptionBuilder;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

public class CommandLineArgs {
	final String mToolchainDirPath;

	public String getToolchainDirPath() {
		return mToolchainDirPath;
	}

	public String getInputDirPath() {
		return mInputDirPath;
	}

	public String getSettingsFilePath() {
		return mSettingsFilePath;
	}

	final String mInputDirPath;
	final String mSettingsFilePath;

	private CommandLineArgs(String toolchainDir, String inputDir, String settingsDir) {
		this.mToolchainDirPath = toolchainDir;
		this.mInputDirPath = inputDir;
		this.mSettingsFilePath = settingsDir;
	}

	public static CommandLineArgs parse(String[] args) throws ParseException {
		// Alter Java ist eine dermaßeen Verbose kacke, ich werde Wahnsinnig.
		// Dieser hauffen FUCK Code hier macht schon, dass ich mir am liebsten
		// die Augen ausstechen möchte.
		// Von dem Krempel im CLI Controller ganz zu schweigen! Wie können
		// Menschen mit diesem shit produktiv arbeiten?

		CommandLine commandLine;
		Option option_tc = OptionBuilder.withArgName("tc").hasArg().withDescription("path containing toolchains")
				.create("TC");
		Option option_input = OptionBuilder.withArgName("i").hasArgs().withDescription("Input Files").create("I");
		Option option_setting = OptionBuilder.withArgName("s").hasArg().withDescription("The S option").create("S");
		Options options = new Options();
		CommandLineParser parser = new GnuParser();

		options.addOption(option_tc);
		options.addOption(option_input);
		options.addOption(option_setting);

		commandLine = parser.parse(options, args);

		if (!(commandLine.hasOption("TC"))) // && commandLine.hasOption("I") &&
											// commandLine.hasOption("S")
			throw new ParseException("required parameters missing and also Java sucks.");

		return new CommandLineArgs(commandLine.getOptionValue("TC"), null, null);
	}

}
