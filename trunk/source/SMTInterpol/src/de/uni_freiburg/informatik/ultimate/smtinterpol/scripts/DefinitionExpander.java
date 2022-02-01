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
package de.uni_freiburg.informatik.ultimate.smtinterpol.scripts;

import java.io.IOException;

import de.uni_freiburg.informatik.ultimate.logic.FormulaLet;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet.UnletType;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;

public class DefinitionExpander extends LoggingScript {

	private final FormulaUnLet mUnletter = new FormulaUnLet(
			UnletType.EXPAND_DEFINITIONS);
	private final FormulaLet mLetter = new FormulaLet();

	public DefinitionExpander(String outfile) throws IOException {
		super(outfile, true);
	}

	@Override
	public LBool assertTerm(Term term) throws SMTLIBException {
		return super.assertTerm(mLetter.let(mUnletter.unlet(term)));
	}

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		final String infile = args[0];
		final String outfile = args[1];
		final OptionMap options = new OptionMap(new DefaultLogger(), true);
		try {
			final ParseEnvironment pe = new ParseEnvironment(
					new DefinitionExpander(outfile), options);
			pe.parseScript(infile);
		} catch (final IOException e) {
			e.printStackTrace();
		}
	}

}
