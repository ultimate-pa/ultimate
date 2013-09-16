/*
 * Copyright (C) 2009-2013 University of Freiburg
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

import java.io.FileNotFoundException;

import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

public class InputTruncation {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		System.setProperty("smtinterpol.ddfriendly", "on");
		String infile = args[0];
		String outfile = args[1];
		try {
			ParseEnvironment pe = new ParseEnvironment(
					new LoggingScript(new SMTInterpol(), outfile, true));
			pe.parseScript(infile);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
	}

}
