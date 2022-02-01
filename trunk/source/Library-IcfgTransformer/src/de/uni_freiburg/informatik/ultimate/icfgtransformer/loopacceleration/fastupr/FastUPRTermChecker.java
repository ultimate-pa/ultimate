/*
 * Copyright (C) 2017 Jill Enke (enkei@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctConjunction;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctagonCalculator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 *
 * @author Jill Enke (enkei@informatik.uni-freiburg.de)
 *
 */
public class FastUPRTermChecker {

	private final ManagedScript mManagedScript;
	private final OctagonCalculator mCalc;
	private Map<IProgramVar, TermVariable> mInVars;
	private Map<IProgramVar, TermVariable> mOutVars;
	private OctConjunction mConjunc;
	private final Script mScript;
	private final FastUPRTermTransformer mTermTransformer;

	/**
	 *
	 * @param utils
	 * @param managedScript
	 * @param calc
	 * @param formulaBuilder
	 * @param services
	 */
	public FastUPRTermChecker(final FastUPRUtils utils, final ManagedScript managedScript, final OctagonCalculator calc,
			final FastUPRFormulaBuilder formulaBuilder, final IUltimateServiceProvider services) {
		mCalc = calc;
		mManagedScript = managedScript;
		mScript = mManagedScript.getScript();
		mTermTransformer = new FastUPRTermTransformer(mScript);
	}

	public void setConjunction(final OctConjunction conjunc) {
		mConjunc = conjunc;
	}

	/**
	 *
	 * @param conjunc
	 * @param inVars
	 * @param outVars
	 */
	public void setConjunction(final OctConjunction conjunc, final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars) {
		mConjunc = conjunc;
		mInVars = inVars;
		mOutVars = outVars;
	}

	public void setInVars(final Map<IProgramVar, TermVariable> inVars) {
		mInVars = inVars;
	}

	public void setOutVars(final Map<IProgramVar, TermVariable> outVars) {
		mOutVars = outVars;
	}

	/**
	 *
	 * @param b
	 * @param c
	 * @return
	 */
	public int checkConsistency(final int b, final int c) {
		for (int k = 0; k <= 2; k++) {
			if (!checkSequentialized(b + (k * c))) {
				return k;
			}
		}
		return -1;
	}

	private boolean checkSequentialized(final int count) {
		final Script script = mManagedScript.getScript();
		final OctConjunction toCheck = mCalc.sequentialize(mConjunc, mInVars, mOutVars, count);
		return checkTerm(toCheck.toTerm(script));

	}

	/**
	 * Checks a term including Quantifiers for satisfiability.
	 *
	 * @param term
	 *            The term to check.
	 * @return TRUE if the term is satisfiable, FALSE if unknown or unsatisfiable.
	 */
	public boolean checkQuantifiedTerm(final Term term) {
		final Term withOutReal = mTermTransformer.transformToInt(term);
		final LBool result = SmtUtils.checkSatTerm(mScript, withOutReal);
		return result != LBool.UNSAT;
	}

	/**
	 * Checks a term for satisfiability.
	 *
	 * @param term
	 *            The term to check.
	 * @return TRUE if the term is satisfiable, FALSE if unknown or unsatisfiable.
	 */
	public boolean checkTerm(final Term term) {

		final Term withOutReal = mTermTransformer.transformToInt(term);

		final LBool result = SmtUtils.checkSatTerm(mScript, withOutReal);
		return result.equals(LBool.SAT);

	}

}
