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
package de.uni_freiburg.informatik.ultimate.cli;

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
	public static final String OPTION_NAME_INPUTFILES = "i";
	public static final String OPTION_NAME_SETTINGS = "s";
	public static final String OPTION_NAME_HELP = "h";

	static List<Option> createCommandLineOptions() {
		// add CLI options
		final List<Option> rtr = new ArrayList<>();
		rtr.add(Option.builder(CommandLineOptions.OPTION_NAME_TOOLCHAIN).longOpt("toolchain").type(File.class).hasArg()
				.required().argName("FILE").build());
		rtr.add(Option.builder(CommandLineOptions.OPTION_NAME_INPUTFILES).longOpt("input").hasArgs().required()
				.argName("FILE").build());
		rtr.add(Option.builder(CommandLineOptions.OPTION_NAME_SETTINGS).longOpt("settings").type(File.class).hasArg()
				.argName("FILE").build());
		rtr.add(Option.builder(CommandLineOptions.OPTION_NAME_HELP).longOpt("help").type(Boolean.class).build());
		return rtr;
	}
}
