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

import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctagonCalculator;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctagonConjunction;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 *
 * @author Jill Enke (enkei@informatik.uni-freiburg.de)
 *
 */
public class TermChecker {

	private final FastUPRUtils mUtils;
	private final ManagedScript mManagedScript;
	private final OctagonCalculator mCalc;
	private Map<IProgramVar, TermVariable> mInVars;
	private Map<IProgramVar, TermVariable> mOutVars;
	private OctagonConjunction mConjunc;
	private final FastUPRFormulaBuilder mFormulaBuilder;
	private final Script mScript;

	public TermChecker(final FastUPRUtils utils, final ManagedScript managedScript, final OctagonCalculator calc,
			final FastUPRFormulaBuilder formulaBuilder) {
		mFormulaBuilder = formulaBuilder;
		mCalc = calc;
		mManagedScript = managedScript;
		mUtils = utils;
		mScript = mManagedScript.getScript();
	}

	public void setConjunction(final OctagonConjunction conjunc) {
		mConjunc = conjunc;
	}

	public void setConjunction(final OctagonConjunction conjunc, final Map<IProgramVar, TermVariable> inVars,
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
		final OctagonConjunction toCheck = mCalc.sequentialize(mConjunc, mInVars, mOutVars, count);
		return checkTerm(toCheck.toTerm(script));

	}

	public boolean checkTerm(final Term term) {
		mScript.push(1);

		try {
			mScript.assertTerm(getClosedTerm(term));
		} catch (final Exception e) {
			mUtils.debug(e.getClass().toString());
			mUtils.debug(e.toString());
		}
		final LBool result = mScript.checkSat();

		mScript.pop(1);

		return result.equals(LBool.SAT);
	}

	private Term getClosedTerm(final Term term) {
		final UnmodifiableTransFormula formula = mFormulaBuilder.buildTransFormula(term, mInVars, mOutVars);
		return formula.getClosedFormula();
	}

}
