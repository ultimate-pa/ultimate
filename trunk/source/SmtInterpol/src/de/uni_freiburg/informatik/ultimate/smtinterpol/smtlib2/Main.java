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
package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2;

import java.math.BigInteger;

import org.apache.log4j.Logger;

public class Main {
	
	private static void usage() {
		System.err.println("USAGE smtinterpol [-q] [-v] [-t <num>] [-r <num>] [file.smt2]");
	}
	
	public static void main(String[] param) {
		Logger logger = Logger.getRootLogger();
        int paramctr = 0;
        SMTInterpol benchmark = new SMTInterpol(logger, true);
        while (paramctr < param.length
        		&& param[paramctr].startsWith("-")) {
        	if (param[paramctr].equals("--")) {
        		paramctr++;
        		break;
        	} else if (param[paramctr].equals("-v")) {
        		benchmark.setOption(":verbosity", BigInteger.valueOf(5));
        		paramctr++;
        	} else if (param[paramctr].equals("-q")) {
        		benchmark.setOption(":verbosity", BigInteger.valueOf(3));
        		paramctr++;
        	} else if (param[paramctr].equals("-t") && 
        			++paramctr < param.length) {
        		try {
        			int timeout = Integer.parseInt(param[paramctr]);
        			if (timeout < 0) {
        				logger.error("Cannot parse timeout " +
        						"argument: Negative number");
        			} else {
        				benchmark.setOption(":timeout", BigInteger.valueOf(timeout));
        			}
        		} catch (NumberFormatException nfe) {
    				logger.error("Cannot parse timeout " +
        					"argument: Not a number");
        		}
        		paramctr++;
        	} else if (param[paramctr].equals("-r") &&
        			++paramctr < param.length) {
        		try {
        			int seed = Integer.parseInt(param[paramctr]);
        			if (seed < 0) {
        				logger.error("Cannot parse random seed " +
        						"argument: Negative number");
        			} else {
        				benchmark.setOption(":random-seed", BigInteger.valueOf(seed));
        			}
        		} catch (NumberFormatException nfe) {
    				logger.error("Cannot parse random seed " +
        					"argument: Not a number");
        		}
        		paramctr++;
        	} else {
        		usage();
        		return;
        	}
        }
		String filename;
		if (paramctr < param.length) {
			filename = param[paramctr++];
		} else {
			filename = "<stdin>";
		}
		if (paramctr != param.length) {
			usage();
			return;
		}
        ParseEnvironment parseEnv = new ParseEnvironment(benchmark);
        parseEnv.parseScript(filename);
	}
}
