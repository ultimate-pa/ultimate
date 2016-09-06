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

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ExitHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;

public class Prepare implements ExitHook {

	Script mScript;
	
	/**
	 * @param args
	 * @throws FileNotFoundException 
	 */
	public static void main(String[] args) throws FileNotFoundException {
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
		final Prepare exit = new Prepare();
		final DefaultLogger logger = new DefaultLogger();
		final OptionMap options = new OptionMap(logger, true);
		while (fileStartIdx < args.length) {
			final StringBuilder target = new StringBuilder(args[fileStartIdx]);
			// Insert .prep before .smt2
			target.insert(target.length() - 5, ".prep");// NOCHECKSTYLE
			options.reset();
			final ParseEnvironment pe = new ParseEnvironment(exit.mScript =
					new PrepareScript(track, target.toString()), exit,
					options);
			pe.parseScript(args[fileStartIdx]);
			++fileStartIdx;
		}
	}

	@Override
	public void exitHook() {
		mScript.exit();
	}

}
