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

import java.io.IOException;

import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ErrorCallback;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

public final class InputTruncation {

	private InputTruncation() {
		// Hide constructor
	}

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		final String infile = args[0];
		final String outfile = args[1];
		try {
			final DefaultLogger logger = new DefaultLogger();
			final OptionMap options = new OptionMap(logger, true);
			final SMTInterpol smtinterpol = new SMTInterpol(logger);
			final ParseEnvironment pe = new ParseEnvironment(
					new LoggingScript(smtinterpol, outfile, true),
					options);
			smtinterpol.setErrorCallback(new ErrorCallback() {
				@Override
				public void notifyError(ErrorReason reason) {
					System.exit(reason.ordinal() + 1);
				}
			});
			pe.parseScript(infile);
		} catch (final IOException e) {
			e.printStackTrace();
		}
	}

}
