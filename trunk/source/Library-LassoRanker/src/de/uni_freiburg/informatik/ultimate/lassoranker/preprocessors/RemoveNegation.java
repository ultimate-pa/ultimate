/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE LassoRanker Library.
 * 
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormula;


/**
 * Remove negation before atoms.
 * 
 * <ul>
 * <li> NOT (a >= b) becomes a < b
 * <li> NOT (a > b) becomes a <= b
 * </ul>
 * 
 * @author Jan Leike
 */
public class RemoveNegation extends TransformerPreprocessor {
	
	public static final String s_Description = "Remove negation before atoms";
	@Override
	public String getDescription() {
		return s_Description;
	}
	
	@Override
	protected boolean checkSoundness(Script script, ModifiableTransFormula oldTF,
			ModifiableTransFormula newTF) {
		final Term old_term = oldTF.getFormula();
		final Term new_term = newTF.getFormula();
		return LBool.SAT != Util.checkSat(script,
				script.term("distinct", old_term, new_term));
	}
	
	@Override
	protected TermTransformer getTransformer(Script script) {
		return new RemoveNegationTransformer(script);
	}
	
	private class RemoveNegationTransformer extends TermTransformer {
		
		private final Script mScript;
		
		RemoveNegationTransformer(Script script) {
			super();
			assert script != null;
			mScript = script;
		}
		
		@Override
		protected void convert(Term term) {
			if (term instanceof ApplicationTerm) {
				final ApplicationTerm appt = (ApplicationTerm) term;
				if (appt.getFunction().getName().equals("not")) {
					assert(appt.getParameters().length == 1);
					final Term param = appt.getParameters()[0];
					assert(param instanceof ApplicationTerm);
					final ApplicationTerm appt2 = (ApplicationTerm)param;
					if (appt2.getFunction().getName().equals("<=")) {
						setResult(mScript.term(">", appt2.getParameters()));
					} else if (appt2.getFunction().getName().equals("<")) {
						setResult(mScript.term(">=", appt2.getParameters()));
					} else if (appt2.getFunction().getName().equals(">=")) {
						setResult(mScript.term("<", appt2.getParameters()));
					} else if (appt2.getFunction().getName().equals(">")) {
						setResult(mScript.term("<=", appt2.getParameters()));
					} else {
						assert(false);
					}
					return;
				}
			}
			super.convert(term);
		}
	}
}
