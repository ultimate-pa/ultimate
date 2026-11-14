/*
 * Copyright (C) 2020 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.arrays.ElimStorePlain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.arrays.ElimStorePlain.ElimStorePlainException;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Smart array Ackermanization.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class DualJunctionSaa extends DualJunctionQuantifierElimination {

	/**
	 * Our array elimination does not support if the term of the elimination task contains quantified formulas. If this
	 * variable is set, we bring the term in prenex normal form. Apply the elimination to the "matrix" of the prenex
	 * normal form and add prepend the quantifiers to the result. If the elimination new introduces auxiliary quantified
	 * variables, these have to be added at the same level as the eliminatee, i.e., have to be prepended to the result.
	 * If this variable is not set the elimination may crash or return unsound results.
	 */
	private static final boolean PRENEX_NORMAL_FORM_FOR_INNERQUANTIFIERS = true;

	/**
	 * @see constructor
	 */
	private final boolean mExpensiveEliminations;

	/**
	 * @param expensiveEliminations
	 */
	public DualJunctionSaa(final ManagedScript script, final IUltimateServiceProvider services,
			final boolean expensiveEliminations) {
		super(script, services);
		mExpensiveEliminations = expensiveEliminations;
	}

	@Override
	public String getName() {
		return "smart array ackermanization";
	}

	@Override
	public String getAcronym() {
		return "saa";
	}

	@Override
	public EliminationResult tryToEliminate(final EliminationTask inputEt) {
		return tryToEliminateSomeArrayEliminatee(inputEt);
	}

	private EliminationResult tryToEliminateSomeArrayEliminatee(final EliminationTask inputEt) {
		for (final TermVariable eliminatee : inputEt.getEliminatees()) {
			if (!SmtSortUtils.isArraySort(eliminatee.getSort())) {
				continue;
			}
			// We new a new context in which all other eliminatees are considered bound by ancestors.
			Context newContext;
			{
				final HashSet<TermVariable> boundByAncestors =
						new HashSet<>(inputEt.getContext().getBoundByAncestors());
				for (final TermVariable tv : inputEt.getEliminatees()) {
					if (tv != eliminatee) {
						boundByAncestors.add(tv);
					}
				}
				newContext = new Context(inputEt.getContext().getCriticalConstraint(), boundByAncestors);
			}
			final EliminationTask singletonEliminationTask = new EliminationTask(inputEt.getQuantifier(),
					Collections.singleton(eliminatee), inputEt.getTerm(), newContext);
			final EliminationResult er = tryToEliminateArrayEliminateeStep1(singletonEliminationTask);
			if (er != null) {
				assert newContext == er.getEliminationTask().getContext() : "illegal change of context";
				return new EliminationResult(new EliminationTask(inputEt.getQuantifier(), inputEt.getEliminatees(),
						er.getEliminationTask().getTerm(), inputEt.getContext()), er.getNewEliminatees());
			}
		}
		// No array eliminatee.
		return null;
	}

	private EliminationResult tryToEliminateArrayEliminateeStep1(final EliminationTask inputEt) {
		final Pair<Term, EliminationTask> pair = inputEt.makeTight(mServices, mMgdScript);
		if (pair == null) {
			// Unable to move out dualJuncts
			return tryToEliminateArrayEliminateeStep2(inputEt);
		}
		final EliminationResult er = tryToEliminateArrayEliminateeStep2(pair.getSecond());
		if (er == null) {
			// Elimination failed
			return null;
		}
		// Elimination succeeded. We have to prepend the dualJuncts that we moved out to the result.
		final Term resultTerm = QuantifierUtils.applyDualFiniteConnective(mScript, inputEt.getQuantifier(),
				pair.getFirst(), er.getEliminationTask().getTerm());
		final EliminationTask resultEliminationTask = new EliminationTask(inputEt.getQuantifier(),
				inputEt.getEliminatees(), resultTerm, inputEt.getContext());
		return new EliminationResult(resultEliminationTask, er.getNewEliminatees());
	}

	private EliminationResult tryToEliminateArrayEliminateeStep2(final EliminationTask inputEt) {
		final EliminationResult er;
		if (PRENEX_NORMAL_FORM_FOR_INNERQUANTIFIERS) {
			er = tryToEliminateArrayEliminateeStep3(inputEt);
		} else {
			er = tryToEliminateArrayEliminateeStep4(inputEt);
		}
		return er;
	}

	// TODO 20261114 Matthias: Fix bound by ancestor handling for calls. Find out how we put together the result for
	// alternating quantifiers.
	private EliminationResult tryToEliminateArrayEliminateeStep3(final EliminationTask inputEt) {
		final Term pnf = new PrenexNormalForm(mMgdScript).transform(inputEt.getTerm());
		final QuantifierSequence qs = new QuantifierSequence(mMgdScript, pnf);
		final EliminationTask et = inputEt.update(qs.getInnerTerm());
		final EliminationResult res = tryToEliminateArrayEliminateeStep4(et);
		if (res == null) {
			return null;
		} else {
			if (qs.getQuantifierBlocks().isEmpty()) {
				return res;
			} else {
				// The new quantifiers have to be innermost.
				// See {@link QuantifierEliminationRegressionTest#suse01}
				// TODO 20220607 Matthias: Difficult decision: Should we do an elimination of
				// inner quantifiers here? See #innerAlternatingFirst
				final EliminationTask etWithNewEliminatees = res.integrateNewEliminatees();
				final QuantifierSequence qsForResult = new QuantifierSequence(mMgdScript,
						etWithNewEliminatees.toTerm(mMgdScript.getScript()), qs.getQuantifierBlocks());
				final Term resultTerm = qsForResult.toTerm();
				return new EliminationResult(etWithNewEliminatees.update(resultTerm), Collections.emptySet());
			}
		}
	}

	private EliminationResult tryToEliminateArrayEliminateeStep4(final EliminationTask inputEt) {
		EliminationResult res1;
		try {
			res1 = ElimStorePlain.applyComplexEliminationRules(mServices, mLogger, mMgdScript, inputEt);
		} catch (final SMTLIBException e) {
			throw new AssertionError(e);
		} catch (final ElimStorePlainException e) {
			if (e.getMessage().equals(ElimStorePlainException.NON_TOP_LEVEL_DER)) {
				res1 = null;
			} else if (e.getMessage().equals(ElimStorePlainException.CAPTURED_INDEX)) {
				if (PRENEX_NORMAL_FORM_FOR_INNERQUANTIFIERS) {
					throw new AssertionError("Captured index although handling of inner quantfiers is set");
				}
				res1 = null;
			} else {
				throw new AssertionError(e);
			}
		}
		final TermVariable eliminatee = inputEt.getEliminatees().iterator().next();
		if ((res1 != null) && Arrays.asList(res1.getEliminationTask().getTerm().getFreeVars()).contains(eliminatee)) {
			throw new AssertionError("Var not eliminated: " + eliminatee + " " + inputEt.toTerm(mScript));
		}
		return res1;
	}

}
