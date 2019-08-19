/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
/*
 * Copyright (C) 2009-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library.  If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;

/**
 * SimplifyDDA extended by support for timeouts.
 *
 * @author Matthias Heizmann
 *
 */
public class SimplifyDDAWithTimeout extends SimplifyDDA {

	private final IUltimateServiceProvider mServices;
	private Term mInputTerm;
	private final Term mContext;
	private long mStartTime;

	public SimplifyDDAWithTimeout(final Script script, final IUltimateServiceProvider services) {
		this(script, true, services);
	}

	public SimplifyDDAWithTimeout(final Script script, final boolean simplifyRepeatedly,
			final IUltimateServiceProvider services) {
		this(script, simplifyRepeatedly, services, null);
	}

	/**
	 * Constructor that allows simplification with respect to a given context. E.g., (= x y) can be simplified to false
	 * if we assume that the term (and (= x 0) (= y 1)) is true. This can be used to apply the simplification only to
	 * subformulas of a formula. E.g., if we have the formula (and (= x 0) (= y 1) (= x y)) we can use the first two
	 * conjuncts as a (conjunctive) context and simplify only the third conjunct.
	 *
	 * @param context
	 *            Term that defines under which assumptions the simplification is done.
	 */
	public SimplifyDDAWithTimeout(final Script script, final boolean simplifyRepeatedly,
			final IUltimateServiceProvider services, final Term context) {
		super(script, simplifyRepeatedly);
		mServices = services;
		mContext = context;
	}

	@Override
	protected Redundancy getRedundancy(final Term term) {
		if (!mServices.getProgressMonitorService().continueProcessing()) {
			throw new ToolchainCanceledException(this.getClass(), "simplifying term of DAG size "
					+ (new DAGSize().size(mInputTerm)) + " for " + getElapsedTimeInMilliseconds() + "ms.");
		}
		return super.getRedundancy(term);
	}

	/**
	 * Copy&paste from original method where I removed the checktype modification which is only supported by
	 * SMTInterpol.
	 */
	@Override
	public LBool checkEquivalence(final Term termA, final Term termB) {
		final Term equivalentTestTerm = mScript.term("=", termA, termB);
		final LBool areTermsEquivalent = Util.checkSat(mScript, Util.not(mScript, equivalentTestTerm));
		return areTermsEquivalent;
	}

	/**
	 * Copy&paste from original methods where I commented the assertions about the push-pop stack which are only
	 * supported by SMTInterpol. Furthermore, the assertion that checks the equivalence of the result was weakened. It
	 * now passes also if the result is UNKNOWN.
	 */
	@Override
	public Term getSimplifiedTerm(final Term inputTerm) {
		mInputTerm = inputTerm;
		mStartTime = System.nanoTime();
		// mLogger.debug("Simplifying " + term);
		/* We can only simplify boolean terms. */
		if (!SmtSortUtils.isBoolSort(inputTerm.getSort())) {
			return inputTerm;
		}
		// int lvl = 0;// Java requires initialization
		// assert (lvl = PushPopChecker.currentLevel(mScript)) >= -1;
		Term term = inputTerm;
		mScript.echo(new QuotedObject("Begin Simplifier"));
		mScript.push(1);
		final Collection<TermVariable> freeVars;
		if (mContext == null) {
			freeVars = Arrays.asList(inputTerm.getFreeVars());
		} else {
			freeVars = new HashSet<>(Arrays.asList(inputTerm.getFreeVars()));
			freeVars.addAll(Arrays.asList(mContext.getFreeVars()));
		}

		final Map<TermVariable, Term> substitutionMapping = SmtUtils.termVariables2Constants(mScript, freeVars, true);
		final TermVariable[] vars = new TermVariable[substitutionMapping.size()];
		final Term[] values = new Term[substitutionMapping.size()];
		int offset = 0;
		for (final Entry<TermVariable, Term> entry : substitutionMapping.entrySet()) {
			vars[offset] = entry.getKey();
			values[offset] = entry.getValue();
			offset++;
		}

		if (mContext != null) {
			final Term contextClosed = new FormulaUnLet().unlet(mScript.let(vars, values, mContext));
			mScript.assertTerm(contextClosed);
		}

		term = mScript.let(vars, values, term);

		term = new FormulaUnLet().unlet(term);

		Term output = simplifyOnce(term);
		if (mSimplifyRepeatedly) {
			while (output != term) {
				term = output;
				output = simplifyOnce(term);
			}
		} else {
			term = output;
		}

		term = new TermTransformer() {
			@Override
			public void convert(Term tterm) {
				for (int i = 0; i < vars.length; i++) {
					if (tterm == values[i]) {
						tterm = vars[i];
					}
				}
				super.convert(tterm);
			}
		}.transform(term);// NOCHECKSTYLE
		mScript.pop(1);
		assert mContext != null || checkEquivalence(inputTerm, term) != LBool.SAT : "Simplification unsound?";
		mScript.echo(new QuotedObject("End Simplifier"));
		// assert PushPopChecker.atLevel(mScript, lvl);
		mInputTerm = null;
		return term;
	}

	private long getElapsedTimeInMilliseconds() {
		return (System.nanoTime() - mStartTime) / 1000000;
	}

}
