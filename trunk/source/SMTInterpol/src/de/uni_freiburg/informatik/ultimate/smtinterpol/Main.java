/*
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol;

import java.util.ArrayDeque;
import java.util.Deque;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.smtinterpol.aiger.AIGERFrontEnd;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dimacs.DIMACSParser;
import de.uni_freiburg.informatik.ultimate.smtinterpol.muses.MusEnumerationScript;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib.SMTLIBParser;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ErrorCallback;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTLIB2Parser;

/**
 * Generic frontend that dispatches to the different parsers supported by
 * SMTInterpol.
 * @author Juergen Christ
 */
public final class Main {
	private Main() {
		// Hide constructor
	}

	private static void usage() {
		System.err.println("USAGE: smtinterpol [OPTION]... [INPUTFILE]");
		System.err.println("If no INPUTFILE is given, stdin is used.");
		System.err.println("  -script <class>      Send the input to another Java class implementing Script.");
		System.err.println("  -ddfriendly          Exit with error code indicating problems (delta-debugger friendly).");
		System.err.println("  -no-success          Don't print success messages.");
		System.err.println("  -o <opt>=<value>     Set option :opt to value. The default value is true.");
		System.err.println("  -q                   Only print error messages.");
		System.err.println("  -w                   Don't print statistics and models.");
		System.err.println("  -v                   Print debugging messages.");
		System.err.println("  -t <num>             Set the timeout per check-sat call to <num> milliseconds.");
		System.err.println("  -l <num>             Set the reproducible resource limit per check-sat call to <num>.");
		System.err.println("  -r <num>             Use a different random seed.");
		System.err.println("  -smt2                Parse input as SMTLIB 2 script.");
		System.err.println("  -smt                 Parse input as SMTLIB 1 benchmark.");
		System.err.println("  -d                   Parse input as DIMACS benchmark.");
		System.err.println("  -version             Print version and exit.");
	}

	private static void version() {
		System.err.println("SMTInterpol " + Version.VERSION);
	}

	/**
	 * @param param Command line arguments.
	 */
	public static void main(final String[] param) throws Exception {
		final DefaultLogger logger = new DefaultLogger();
		final OptionMap options = new OptionMap(logger, true);
		final Deque<Option> optionList = new ArrayDeque<>();
		boolean useRemus = false;
		ErrorCallback errorCallback = null;
		IParser parser = new SMTLIB2Parser();
		Script solver = null;
		int paramctr = 0;
		while (paramctr < param.length
				&& param[paramctr].startsWith("-")) {
			if (param[paramctr].equals("--")) {
				paramctr++;
				break;
			} else if (param[paramctr].equals("-script")
					&& paramctr + 1 < param.length) {
				paramctr++;
				String scriptName = param[paramctr];
				if (!scriptName.contains(".")) {
					scriptName = "de.uni_freiburg.informatik.ultimate.smtinterpol.scripts." + scriptName;
				}
				final Class<?> scriptClass = Class.forName(scriptName);
				solver = (Script) scriptClass.newInstance();
			} else if (param[paramctr].equals("-ddfriendly")) {
				errorCallback = new ErrorCallback() {
					@Override
					public void notifyError(final ErrorReason reason) {
						System.exit(reason.ordinal() + 1);
					}
				};
			} else if (param[paramctr].equals("-remus")) {
				useRemus = true;
			} else if (param[paramctr].equals("-no-success")) {
				optionList.add(new Option(":print-success", false));
			} else if (param[paramctr].equals("-v")) {
				optionList.add(new Option(":verbosity", LogProxy.LOGLEVEL_DEBUG));
			} else if (param[paramctr].equals("-w")) {
				optionList.add(new Option(":verbosity", LogProxy.LOGLEVEL_WARN));
			} else if (param[paramctr].equals("-q")) {
				optionList.add(new Option(":verbosity", LogProxy.LOGLEVEL_ERROR));
			} else if (param[paramctr].equals("-t")
					&& ++paramctr < param.length) {
				optionList.add(new Option(":timeout", param[paramctr]));
			} else if (param[paramctr].equals("-l")
					&& ++paramctr < param.length) {
				optionList.add(new Option(":reproducible-resource-limit", param[paramctr]));
			} else if (param[paramctr].equals("-r")
					&& ++paramctr < param.length) {
				optionList.add(new Option(":random-seed", param[paramctr]));
			} else if (param[paramctr].equals("-o")
					&& paramctr + 1 < param.length) {
				paramctr++;
				final String opt = param[paramctr];
				final int eq = opt.indexOf('=');
				String name;
				Object value;
				if (eq == -1) {
					name = opt;
					value = Boolean.TRUE;
				} else {
					name = opt.substring(0, eq);
					value = opt.substring(eq + 1);
				}
				try {
					optionList.add(new Option(":" + name, value));
				} catch (final UnsupportedOperationException ex) {
					System.err.println("Unknown option :" + name + ".");
					return;
				} catch (final SMTLIBException ex) {
					System.err.println(ex.getMessage());
					return;
				}
			} else if (param[paramctr].equals("-smt2")) {
				parser = new SMTLIB2Parser();
			} else if (param[paramctr].equals("-smt")) {
				parser = new SMTLIBParser();
			} else if (param[paramctr].equals("-d")) {
				parser = new DIMACSParser();
			} else if (param[paramctr].equals("-a")) {
				parser = new AIGERFrontEnd();
			} else if (param[paramctr].equals("-trace")) {
				optionList.add(new Option(":verbosity", LogProxy.LOGLEVEL_TRACE));
			} else if (param[paramctr].equals("-version")) {
				version();
				return;
			} else {
				usage();
				return;
			}
			++paramctr;
		}
		String filename = null;
		if (paramctr < param.length) {
			filename = param[paramctr++];
		}
		if (paramctr != param.length) {
			usage();
			return;
		}
		if (solver == null) {
			final SMTInterpol smtinterpol = new SMTInterpol(null, options);
			smtinterpol.setErrorCallback(errorCallback);
			solver = smtinterpol;
			if (useRemus) {
				solver = new MusEnumerationScript(smtinterpol);
			}
		}
		for (final Option opt : optionList) {
			solver.setOption(opt.getName(), opt.getValue());
		}
		options.started();
		final int exitCode = parser.run(solver, filename, options);
		System.exit(exitCode);
	}

	/**
	 * Class to store an option name value pair.
	 *
	 * @author Jochen Hoenicke
	 */
	private static class Option {
		String mName;
		Object mValue;

		public Option(final String name, final Object value) {
			mName = name;
			mValue = value;
		}

		public String getName() {
			return mName;
		}

		public Object getValue() {
			return mValue;
		}
	}
}
