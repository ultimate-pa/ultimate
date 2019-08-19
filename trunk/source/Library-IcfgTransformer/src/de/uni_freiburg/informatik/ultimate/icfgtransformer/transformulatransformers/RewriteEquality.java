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

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Util;

/**
 * Replaces equalities (atoms of the form a = b) with (a ≤ b /\ a ≥ b) and inequalities (a != b) with (a > b \/ a < b).
 *
 * @author Jan Leike
 */
public class RewriteEquality extends TransformerPreprocessor {

	public static final String DESCRIPTION =
			"Replaces a = b with (a <= b /\\ a >= b) and a != b with (a > b \\/ a < b)";

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
		return new RewriteEqualityTransformer(script.getScript());
	}

	private static final class RewriteEqualityTransformer extends TermTransformer {

		private static final Set<String> SUPPORTED_SORTS =
				new HashSet<>(Arrays.asList(new String[] { SmtSortUtils.INT_SORT, SmtSortUtils.REAL_SORT }));
		private final Script mScript;

		RewriteEqualityTransformer(final Script script) {
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
			final String funName = appt.getFunction().getName();
			if (!"=".equals(funName) && !"distinct".equals(funName)) {
				super.convert(term);
				return;
			}
			final String paramSortName = appt.getParameters()[0].getSort().getName();

			if (!SUPPORTED_SORTS.contains(paramSortName)) {
				setResult(term);
				return;
			}

			if ("=".equals(funName)) {
				assert appt.getParameters().length == 2 : "equality with more than two parameters not yet supported";
				final Term param1 = mScript.term("<=", appt.getParameters());
				final Term param2 = mScript.term(">=", appt.getParameters());
				setResult(mScript.term("and", param1, param2));
				return;
			} else if ("distinct".equals(funName)) {
				assert appt.getParameters().length == 2 : "distinct with more than two parameters not yet supported";
				final Term param1 = mScript.term("<", appt.getParameters());
				final Term param2 = mScript.term(">", appt.getParameters());
				setResult(mScript.term("or", param1, param2));
				return;
			}

		}
	}
}
