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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.io.FileNotFoundException;

import de.uni_freiburg.informatik.ultimate.logic.FormulaLet;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet.UnletType;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;

public class CompilerTest {

	public static class MyLoggingScript extends LoggingScript {
		public MyLoggingScript(final String filename) throws FileNotFoundException {
			super(filename, false);
		}

		@Override
		public LBool assertTerm(Term term) {
			term = new FormulaUnLet(UnletType.EXPAND_DEFINITIONS).unlet(term);
			term = new TermCompiler().transform(term);
			term = new FormulaLet().let(term);
			return super.assertTerm(term);
		}
	}

	public static void main(final String[] param) throws Exception {
		int paramctr = 0;
		String infilename, outfilename;
		if (paramctr < param.length) {
			infilename = param[paramctr++];
		} else {
			infilename = "<stdin>";
		}
		if (paramctr < param.length) {
			outfilename = param[paramctr++];
		} else {
			outfilename = "<stdout>";
		}
		if (paramctr != param.length) {
			usage();
			return;
		}
		final DefaultLogger logger = new DefaultLogger();
		final OptionMap options = new OptionMap(logger, true);
		final Script script = new MyLoggingScript(outfilename);
		final ParseEnvironment parseEnv = new ParseEnvironment(script, options);
		parseEnv.parseScript(infilename);
		parseEnv.exit();
	}

	private static void usage() {
		System.err.println("USAGE smtinterpol [file.smt] [output.smt]");
	}

	private CompilerTest() {
		// Hide constructor
	}
}
