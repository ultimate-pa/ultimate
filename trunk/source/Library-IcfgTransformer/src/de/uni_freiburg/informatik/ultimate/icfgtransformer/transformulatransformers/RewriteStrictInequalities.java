/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Util;

/**
 * Replace strict inequalities that compare terms of sort int by equivalent non-strict inequalities. E.g., the term <i>x
 * > 0</i> is replaced by the term <i>x >= 1</i>.
 * 
 * @author Matthias Heizmann, Jan Leike
 */
public class RewriteStrictInequalities extends TransformerPreprocessor {

	public static final String DESCRIPTION = "Replace strict inequalities by non-strict inequalities";

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
		return new RewriteStrictInequalitiesTransformer(script.getScript());
	}

	/**
	 * Replace strict inequalities that compare terms of sort Int by equivalent non-strict inequalities.
	 *
	 */
	private static final class RewriteStrictInequalitiesTransformer extends TermTransformer {

		private final Script mScript;

		RewriteStrictInequalitiesTransformer(final Script script) {
			assert script != null;
			mScript = script;
		}

		@Override
		protected void convert(final Term term) {
			if (term instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				final String functionSymbolName = appTerm.getFunction().getName();
				Term result = null;
				if (functionSymbolName.equals("<")) {
					result = computeCorrespondingInequality(appTerm);
				} else if (functionSymbolName.equals(">")) {
					result = computeCorrespondingInequality(appTerm);
				}
				if (result != null) {
					setResult(result);
					return;
				}
			}
			super.convert(term);
		}

		/**
		 * Requires that appTerm has function symbol "<" or ">" and that appTerm has two parameters. If the parameters
		 * are of Sort int, we return the corresponding equivalent non-strict inequality. Otherwise we return null.
		 */
		private Term computeCorrespondingInequality(final ApplicationTerm appTerm) {
			final String functionSymbolName = appTerm.getFunction().getName();
			if (appTerm.getParameters().length != 2) {
				throw new AssertionError("expected binary terms");
			}
			if (!SmtSortUtils.isIntSort(appTerm.getParameters()[0].getSort())) {
				return null;
			}
			final Term one = SmtUtils.constructIntValue(mScript, BigInteger.ONE);
			Term result;
			if (functionSymbolName.equals("<")) {
				result = mScript.term("<=", mScript.term("+", appTerm.getParameters()[0], one),
						appTerm.getParameters()[1]);
			} else if (functionSymbolName.equals(">")) {
				result = mScript.term(">=", appTerm.getParameters()[0],
						mScript.term("+", appTerm.getParameters()[1], one));
			} else {
				throw new AssertionError();
			}
			return result;
		}
	}
}
