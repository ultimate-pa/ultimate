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
package de.uni_freiburg.informatik.ultimate.smtinterpol.smtcomp;

import java.io.FileNotFoundException;
import java.io.IOException;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.scripts.PrepareScript;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;

public class Prepare {
	/**
	 * @param args
	 * @throws FileNotFoundException
	 */
	public static void main(String[] args) throws IOException {
		Track track = Track.MAIN;
		int fileStartIdx = 0;
		if (args[0].equals("--track")) {
			fileStartIdx = 2;
			if (args[0].equals("main")) {
				track = Track.MAIN;
			} else if (args[1].equals("app")) {
				track = Track.APPLICATION;
			} else if (args[1].equals("core")) {
				track = Track.UNSAT_CORE;
			} else if (args[1].equals("proof")) {
				track = Track.PROOF_GEN;
			} else {
				System.out.println(
				    "USAGE: Prepare [--track <main | app | core | proof>] <files>");
				return;
			}
		}
		final DefaultLogger logger = new DefaultLogger();
		final OptionMap options = new OptionMap(logger, true);
		while (fileStartIdx < args.length) {
			final StringBuilder target = new StringBuilder(args[fileStartIdx]);
			// Insert .prep before .smt2
			target.insert(target.length() - 5, ".prep");// NOCHECKSTYLE
			options.reset();
			final Script script = new PrepareScript(track, target.toString());
			final ParseEnvironment pe = new ParseEnvironment(script, options);
			pe.parseScript(args[fileStartIdx]);
			script.exit();
			++fileStartIdx;
		}
	}
}
