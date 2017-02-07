/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE IcfgTransformer library.
 * 
 * The ULTIMATE IcfgTransformer library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE IcfgTransformer library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE IcfgTransformer library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormula;


/**
 * Replaces equalities (atoms of the form a = b) with (a ≤ b \/ a ≥ b).
 * 
 * @author Jan Leike
 */
public class RewriteEquality extends TransformerPreprocessor {
	
	public static final String s_Description = 
			"Replaces atoms of the form a = b with (a <= b /\\ a >= b)";
	
	@Override
	public String getDescription() {
		return s_Description;
	}
	
	@Override
	public boolean checkSoundness(Script script, ModifiableTransFormula oldTF,
			ModifiableTransFormula newTF) {
		final Term old_term = oldTF.getFormula();
		final Term new_term = newTF.getFormula();
		return LBool.SAT != Util.checkSat(script,
				script.term("distinct", old_term, new_term));
	}
	
	@Override
	protected TermTransformer getTransformer(Script script) {
		return new RewriteEqualityTransformer(script);
	}
	
	private class RewriteEqualityTransformer extends TermTransformer {
		
		private final Script mScript;
		
		RewriteEqualityTransformer(Script script) {
			assert script != null;
			mScript = script;
		}
		
		@Override
		protected void convert(Term term) {
			if (term instanceof ApplicationTerm) {
				final ApplicationTerm appt = (ApplicationTerm) term;
				if (appt.getFunction().getName().equals("=") &&
						!appt.getParameters()[0].getSort().getName().equals("Bool")) {
					assert(appt.getParameters().length == 2) : "equality with more than two parameters not yet supported";
					final Term param1 = mScript.term("<=", appt.getParameters());
					final Term param2 = mScript.term(">=", appt.getParameters());
					setResult(mScript.term("and", param1, param2));
					return;
				} else if (appt.getFunction().getName().equals("distinct") &&
						!appt.getParameters()[0].getSort().getName().equals("Bool")) {
					assert(appt.getParameters().length == 2) : "distinct with more than two parameters not yet supported";
					final Term param1 = mScript.term("<", appt.getParameters());
					final Term param2 = mScript.term(">", appt.getParameters());
					setResult(mScript.term("or", param1, param2));
					return;
				}
			}
			super.convert(term);
		}
	}
}
