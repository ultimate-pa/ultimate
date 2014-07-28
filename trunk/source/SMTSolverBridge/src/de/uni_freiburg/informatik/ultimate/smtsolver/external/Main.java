package de.uni_freiburg.informatik.ultimate.smtsolver.external;

import java.io.IOException;
import java.math.BigInteger;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;

public class Main {

	private static void usage() {
		System.err.println("USAGE smtinterpol [-q] [-v] [-t <num>] [-r <num>] [file.smt2]");
	}

	public static void main(String[] param) throws IOException {

		/** Specify the solver command here. **/
		String command = "z3 -smt2 -in";

		Logger logger = Logger.getRootLogger();
		int paramctr = 0;
		Script benchmark;
		if (!command.equals("SMTInterpol"))
			benchmark = new Scriptor(command, logger, null, null);
		else
			benchmark = new SMTInterpol(logger, true);

		while (paramctr < param.length && param[paramctr].startsWith("-")) {
			if (param[paramctr].equals("--")) {
				paramctr++;
				break;
			} else if (param[paramctr].equals("-v")) {
				try {
					benchmark.setOption(":verbosity", BigInteger.valueOf(5));
				} catch (SMTLIBException doesNotHappen) {
				}
				paramctr++;
			} else if (param[paramctr].equals("-q")) {
				try {
					benchmark.setOption(":verbosity", BigInteger.valueOf(3));
				} catch (SMTLIBException doesNotHappen) {
				}
				paramctr++;
			} else if (param[paramctr].equals("-t") && ++paramctr < param.length) {
				try {
					int timeout = Integer.parseInt(param[paramctr]);
					if (timeout < 0) {
						logger.error("Cannot parse timeout " + "argument: Negative number");
					} else {
						try {
							benchmark.setOption(":timeout", BigInteger.valueOf(timeout));
						} catch (SMTLIBException doesNotHappen) {
						}
					}
				} catch (NumberFormatException nfe) {
					logger.error("Cannot parse timeout " + "argument: Not a number");
				}
				paramctr++;
			} else if (param[paramctr].equals("-r") && ++paramctr < param.length) {
				try {
					int seed = Integer.parseInt(param[paramctr]);
					if (seed < 0) {
						logger.error("Cannot parse random seed " + "argument: Negative number");
					} else {
						try {
							benchmark.setOption(":random-seed", BigInteger.valueOf(seed));
						} catch (SMTLIBException doesNotHappen) {
						}
					}
				} catch (NumberFormatException nfe) {
					logger.error("Cannot parse random seed " + "argument: Not a number");
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
		try {
			parseEnv.parseScript(filename);
		} catch (SMTLIBException exc) {
			parseEnv.printError(exc.getMessage());
		}
	}
}