/*
 * Copyright (C) 2009-2012 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.test_generator;


import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;


public final class Main {
    
    private Main() {
        // Hide constructor
    }

	private static void usage() {
		System.err.println("USAGE smtinterpol [-q] [-v] [-t <num>] [-r <num>] [file.smt2]");
	}

	public static void main(String[] param) throws IOException, InterruptedException {

		final DefaultLogger logger = new DefaultLogger();
		int paramctr = 0;

		// Oday: Read multiple files

		String filename;
		PrintWriter outfile;
		if (paramctr < param.length) {
			filename = param[paramctr++];
			outfile = new PrintWriter(param[paramctr++] + "-check.smt2");
		} else {
			filename = "<stdin>";
			outfile = new PrintWriter(System.out);
		}

		final TBenchmark benchmark = new TBenchmark(logger, outfile);
		while (paramctr < param.length && param[paramctr].startsWith("-")) {
			if (param[paramctr].equals("--")) {
				paramctr++;
				break;
			} else if (param[paramctr].equals("-v")) {
				benchmark.setOption(":verbosity", BigInteger.valueOf(5)); // NOCHECKSTYLE
				paramctr++;
			} else if (param[paramctr].equals("-q")) {
				benchmark.setOption(":verbosity", BigInteger.valueOf(3)); // NOCHECKSTYLE
				paramctr++;
			} else if (param[paramctr].equals("-t")
					&& ++paramctr < param.length) {
				try {
					final int timeout = Integer.parseInt(param[paramctr]);
					if (timeout < 0) {
						logger.error("Cannot parse timeout "
								+ "argument: Negative number");
					} else {
						benchmark.setOption(":timeout",
								BigInteger.valueOf(timeout));
					}
				} catch (final NumberFormatException enfe) {
					logger.error("Cannot parse timeout "
							+ "argument: Not a number");
				}
				paramctr++;
			} else if (param[paramctr].equals("-r")
					&& ++paramctr < param.length) {
				try {
					final int seed = Integer.parseInt(param[paramctr]);
					if (seed < 0) {
						logger.error("Cannot parse random seed "
								+ "argument: Negative number");
					} else {
						benchmark.setOption(":random-seed",
								BigInteger.valueOf(seed));
					}
				} catch (final NumberFormatException enfe) {
					logger.error("Cannot parse random seed "
							+ "argument: Not a number");
				}
				paramctr++;
			} else {
				usage();
				return;
			}
		}

		if (paramctr != param.length) {
			usage();
			return;
		}
		
		// JC: Commented this out since it does not work.  Not sure if it is
		//     worth refactoring this.
//		ParseEnvironment env = new ParseEnvironment(benchmark);
//		env.parseScript(filename);
	}
	
	public static List<String> getFiles(File path) {
		final List<String> files = new ArrayList<String>();

		if (path.isFile()) {
			files.add(path.toString());
			return files;
		}
		final File [] children = path.listFiles();
		
		for (int i = 0; i < children.length; i++) {
			if (children[i].isFile()) {
				files.add(children[i].toString());
			} else {
				if (children[i].toString().endsWith(".svn")) {
					continue;
				}
				final File sub = new File(children[i].toString());
				files.addAll(getFiles(sub));
			}
		}
		return files;
	}
}
