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

import de.uni_freiburg.informatik.ultimate.logic.FormulaLet;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet.UnletType;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.TermCompiler;

public class TermCompilerTester extends LoggingScript {
	
	FormulaUnLet mUnletter = new FormulaUnLet(UnletType.EXPAND_DEFINITIONS);
	TermCompiler mCompiler = new TermCompiler();
	FormulaLet mLetter = new FormulaLet();
	
	public TermCompilerTester() throws FileNotFoundException {
		super("<stdout>", true);
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		Term tmp = mUnletter.unlet(term);
		tmp = mCompiler.transform(tmp);
//		Simplifier simp = new Simplifier();
//		Term tmp2;
//		int rounds = 0;
//		do {
//			tmp2 = tmp;
//			tmp = simp.transform(tmp2);
//			++rounds;
//		} while (tmp2 != tmp);
//		System.err.printf("Simplified for %d rounds\n", rounds);
//		System.exit(0);
		return super.assertTerm(mLetter.let(tmp));
	}
	
}
