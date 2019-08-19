/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Util;

/**
 * Remove negation before atoms.
 * 
 * <ul>
 * <li>NOT (a >= b) becomes a < b
 * <li>NOT (a > b) becomes a <= b
 * </ul>
 * 
 * @author Jan Leike
 */
public class RemoveNegation extends TransformerPreprocessor {

	public static final String DESCRIPTION = "Remove negation before atoms";

	@Override
	public String getDescription() {
		return DESCRIPTION;
	}

	@Override
	public boolean checkSoundness(final Script script, final ModifiableTransFormula oldTF,
			final ModifiableTransFormula newTF) {
		final Term oldTerm = oldTF.getFormula();
		final Term newTerm = newTF.getFormula();
		return LBool.SAT != Util.checkSat(script, script.term("distinct", oldTerm, newTerm));
	}

	@Override
	protected TermTransformer getTransformer(final ManagedScript script) {
		return new RemoveNegationTransformer(script.getScript());
	}

	private static final class RemoveNegationTransformer extends TermTransformer {

		private final Script mScript;

		RemoveNegationTransformer(final Script script) {
			super();
			assert script != null;
			mScript = script;
		}

		@Override
		protected void convert(final Term term) {
			if (!(term instanceof ApplicationTerm)) {
				super.convert(term);
				return;
			}
			final ApplicationTerm appt = (ApplicationTerm) term;
			if (!"not".equals(appt.getFunction().getName())) {
				super.convert(term);
				return;
			}
			assert appt.getParameters().length == 1;

			final Term param = appt.getParameters()[0];
			if (!(param instanceof ApplicationTerm)) {
				super.convert(term);
				return;
			}
			final ApplicationTerm appt2 = (ApplicationTerm) param;
			final String funName = appt2.getFunction().getName();
			if ("<=".equals(funName)) {
				setResult(mScript.term(">", appt2.getParameters()));
			} else if ("<".equals(funName)) {
				setResult(mScript.term(">=", appt2.getParameters()));
			} else if (">=".equals(funName)) {
				setResult(mScript.term("<", appt2.getParameters()));
			} else if (">".equals(funName)) {
				setResult(mScript.term("<=", appt2.getParameters()));
			} else {
				setResult(term);
			}

		}
	}
}
