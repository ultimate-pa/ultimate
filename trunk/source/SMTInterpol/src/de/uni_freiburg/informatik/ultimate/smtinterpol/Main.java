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
package de.uni_freiburg.informatik.ultimate.smtinterpol;

import java.io.IOException;
import java.io.InputStream;
import java.math.BigInteger;
import java.util.Properties;

import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.smtinterpol.aiger.AIGERFrontEnd;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dimacs.DIMACSParser;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib.SMTLIBParser;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTLIB2Parser;

/**
 * Generic frontend that dispatches to the different parsers supported by
 * SMTInterpol.
 * @author Juergen Christ
 */
public final class Main {
	
	public static Properties sVersionInfo; //NOCHECKSTYLE
	static {
		sVersionInfo = new Properties();
		try {
			InputStream is = 
					Main.class.getResourceAsStream("Version.properties");
			if (is != null)
				sVersionInfo.load(is);
		} catch (IOException ex) {
			/* ignore */
		}
	}
	
	private Main() {
		// Hide constructor
	}

	public static final String getVersion() {
		String version = sVersionInfo.getProperty("version", "unknown version");
		if (Config.COMPETITION)
			version += "-comp"; // NOPMD
		return version;
	}
	
	private static void usage() {
		System.err.println("USAGE: smtinterpol [OPTION]... [INPUTFILE]");
		System.err.println("If no INPUTFILE is given, stdin is used.");
		System.err.println("  -transform <output>  Transform the input to SMTLIB 2 and write into output.");// NOCHECKSTYLE
		System.err.println("  -script <class>      Send the input to another Java class implementing Script.");// NOCHECKSTYLE
		System.err.println("  -no-success          Don't print success messages.");// NOCHECKSTYLE
		System.err.println("  -q                   Don't print statistics and models.");// NOCHECKSTYLE
		System.err.println("  -v                   Print debugging messages.");
		System.err.println("  -t <num>             Set the timeout per check-sat call to <num> milliseconds.");// NOCHECKSTYLE
		System.err.println("  -r <num>             Use a different random seed.");// NOCHECKSTYLE
		System.err.println("  -smt2                Parse input as SMTLIB 2 script.");// NOCHECKSTYLE
		System.err.println("  -smt                 Parse input as SMTLIB 1 benchmark.");// NOCHECKSTYLE
		System.err.println("  -d                   Parse input as DIMACS benchmark.");// NOCHECKSTYLE
		System.err.println("  -version             Print version and exit.");
	}
	
	private static void version() {
		String date = sVersionInfo.getProperty("build.date");
		System.err.println("SMTInterpol " + getVersion());
		if (date != null)
			System.err.println("  built on " + date);
	}
	
	/**
	 * @param param Command line arguments.
	 */
	public static void main(String[] param) throws Exception {
		BigInteger verbosity = null;
		BigInteger timeout = null;
		BigInteger seed = null;
		IParser parser = new SMTLIB2Parser();
		Script solver = null;
		boolean printSuccess = true;
		int paramctr = 0;
        while (paramctr < param.length
        		&& param[paramctr].startsWith("-")) {
        	if (param[paramctr].equals("--")) {
        		paramctr++;
        		break;
        	} else if (param[paramctr].equals("-transform")
     			   && paramctr + 1 < param.length) {
    			paramctr++;
        		solver = new LoggingScript(param[paramctr], true);
        	} else if (param[paramctr].equals("-script")
     			   && paramctr + 1 < param.length) {
     			paramctr++;
     			Class<?> scriptClass = Class.forName(param[paramctr]);
     			solver = (Script) scriptClass.newInstance();
        	} else if (param[paramctr].equals("-no-success")) {
        		printSuccess = false;
        	} else if (param[paramctr].equals("-v")) {
        		verbosity = BigInteger.valueOf(5);// NOCHECKSTYLE
        	} else if (param[paramctr].equals("-q")) {
        		verbosity = BigInteger.valueOf(2);// NOCHECKSTYLE
        	} else if (param[paramctr].equals("-t")
        			&& ++paramctr < param.length) {
        		try {
        			timeout = new BigInteger(param[paramctr]);
        			if (timeout.signum() <= 0) {
        				timeout = null;
        				System.err.println(
        						"Cannot parse timeout argument: Non-positive number");// NOCHECKSTYLE
        			}
        		} catch (NumberFormatException enfe) {
        			System.err.println("Cannot parse timeout argument: Not a number");// NOCHECKSTYLE
        		}
        	} else if (param[paramctr].equals("-r")
        			&& ++paramctr < param.length) {
        		try {
        			seed = new BigInteger(param[paramctr]);
        			if (seed.signum() < 0) {
        				System.err.println("Cannot parse random seed argument: Negative number");// NOCHECKSTYLE
        				seed = null;
        			}
        		} catch (NumberFormatException enfe) {
    				System.err.println("Cannot parse random seed argument: Not a number");// NOCHECKSTYLE
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
        		verbosity = BigInteger.ONE.negate();
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
		if (paramctr < param.length)
			filename = param[paramctr++];
		if (paramctr != param.length) {
			usage();
			return;
		}
		if (solver == null)
			solver = new SMTInterpol();
		solver.setOption(":print-success", printSuccess);
		if (verbosity != null)
			solver.setOption(":verbosity", verbosity);
		if (timeout != null)
			solver.setOption(":timeout", timeout);
		if (seed != null)
			solver.setOption(":random-seed", seed);
		int exitCode = parser.run(solver, filename);
		System.exit(exitCode);
	}

}
