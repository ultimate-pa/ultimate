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

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.apache.commons.cli.Option;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class CommandLineOptions {

	public static final String OPTION_NAME_TOOLCHAIN = "tc";
	public static final String OPTION_LONG_NAME_TOOLCHAIN = "toolchain";
	public static final String OPTION_NAME_INPUTFILES = "i";
	public static final String OPTION_LONG_NAME_INPUTFILES = "input";
	public static final String OPTION_NAME_SETTINGS = "s";
	public static final String OPTION_LONG_NAME_SETTINGS = "settings";
	public static final String OPTION_NAME_HELP = "h";
	public static final String OPTION_LONG_NAME_VERSION = "version";
	public static final String OPTION_LONG_NAME_EXPERIMENTAL = "experimental";
	public static final String OPTION_LONG_NAME_CSV_DIR = "csv-dir";
	public static final String OPTION_LONG_NAME_GENERATE_CSV = "generate-csv";

	private CommandLineOptions() {
		// this is a utility class
	}

	/**
	 * Create a list of {@link Option}s of the Cli controller that require toolchain and input file to be set.
	 */
	public static List<Option> createCliControllerOptions() {
		return createCliControllerOptions(true, true);
	}

	/**
	 * Create a list of {@link Option}s of the Cli controller.
	 *
	 * @param requireToolchain
	 *            true iff the toolchain option is mandatory
	 * @param requireInputFile
	 *            true iff the input file option is mandatory
	 */
	public static List<Option> createCliControllerOptions(final boolean requireToolchain,
			final boolean requireInputFile) {
		// add CLI options
		final List<Option> rtr = new ArrayList<>();
		rtr.add(Option.builder(OPTION_NAME_TOOLCHAIN).longOpt(OPTION_LONG_NAME_TOOLCHAIN).type(File.class).hasArg()
				.required(requireToolchain).argName("FILE")
				.desc("Specify the path to an Ultimate toolchain file. Depending on the toolchain, you may have more "
						+ "options.")
				.build());
		rtr.add(Option.builder(OPTION_NAME_INPUTFILES).longOpt(OPTION_LONG_NAME_INPUTFILES).hasArgs()
				.required(requireInputFile).argName("FILE").build());
		rtr.add(Option.builder(OPTION_NAME_SETTINGS).longOpt(OPTION_LONG_NAME_SETTINGS).type(File.class).hasArg()
				.argName("FILE").build());
		rtr.add(Option.builder().longOpt(OPTION_LONG_NAME_GENERATE_CSV).type(Boolean.class)
				.desc("Generate .csv files from Statistics results and dump them to a directory (the directory name is "
						+ "chosen based on the filenames of input, toolchain and settings). The .csv files will also "
						+ "contain four additional columns in the beginning for Toolchainfile, Settingsfile, "
						+ "Inputfile, Result")
				.build());
		rtr.add(Option.builder().longOpt(OPTION_LONG_NAME_CSV_DIR).type(File.class)
				.desc("Specify the path to a directory where the generated .csv files should be stored.").hasArg()
				.argName("DIR").build());
		rtr.add(Option.builder(OPTION_NAME_HELP).longOpt("help").type(Boolean.class).build());
		rtr.add(Option.builder().longOpt(OPTION_LONG_NAME_VERSION).type(Boolean.class).build());
		rtr.add(Option.builder().longOpt(OPTION_LONG_NAME_EXPERIMENTAL).type(Boolean.class)
				.desc("Also show experimental options (even if they do not have a description).").build());
		return rtr;
	}
}
