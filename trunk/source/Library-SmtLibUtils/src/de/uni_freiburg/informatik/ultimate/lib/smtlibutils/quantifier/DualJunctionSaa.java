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
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Context;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.arrays.ElimStorePlain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.arrays.ElimStorePlain.ElimStorePlainException;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Smart array Ackermanization.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class DualJunctionSaa extends DualJunctionQuantifierElimination {

	/**
	 * Our array elimination does not support if the term of the elimination task
	 * contains quantified formulas. If this variable is set, we bring the term in
	 * prenex normal form. Apply the elimination to the "matrix" of the prenex
	 * normal form and add prepend the quantifiers to the result. If the elimination
	 * new introduces auxiliary quantified variables, these have to be added at the
	 * same level as the eliminatee, i.e., have to be prepended to the result. If
	 * this variable is not set the elimination may crash or return unsound results.
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
		final EliminationResult er = tryExhaustivelyToEliminate(inputEt);
		return er;
	}

	public EliminationResult tryExhaustivelyToEliminate(final EliminationTask inputEt) {
		final EliminationResult er = tryToEliminateOne(inputEt);
		if (er == null) {
			return null;
		} else {
			return er;
		}
	}

	private EliminationResult tryToEliminateOne(final EliminationTask inputEt) {
		for (final TermVariable eliminatee : inputEt.getEliminatees()) {
			if (!SmtSortUtils.isArraySort(eliminatee.getSort())) {
				continue;
			}
			final EliminationTask singletonEliminationTask = new EliminationTask(inputEt.getQuantifier(),
					Collections.singleton(eliminatee), inputEt.getTerm(), inputEt.getContext());
			final EliminationResult er = tryToEliminateOne1(singletonEliminationTask);
			if (er != null) {
				return new EliminationResult(
						er.getEliminationTask().update(inputEt.getEliminatees(), er.getEliminationTask().getTerm()),
						er.getNewEliminatees());
			}
		}
		return null;
	}

	private EliminationResult tryToEliminateOne1(final EliminationTask inputEt) {
		EliminationResult er;
		if (PRENEX_NORMAL_FORM_FOR_INNERQUANTIFIERS) {
			er = tryToEliminateOne2(inputEt);
		} else {
			er = tryToEliminateOne3(inputEt);
		}
		return er;
	}

	private EliminationResult tryToEliminateOne2(final EliminationTask inputEt) {
		final Term pnf = new PrenexNormalForm(mMgdScript).transform(inputEt.getTerm());
		final QuantifierSequence qs = new QuantifierSequence(mMgdScript.getScript(), pnf);
		final Term term = qs.getInnerTerm();
		final EliminationTask et = inputEt.update(term);
		final EliminationResult res = tryToEliminateOne3(et);
		if (res == null) {
			return null;
		} else {
			final QuantifierSequence qsForResult = new QuantifierSequence(mScript, res.getEliminationTask().getTerm(),
					qs.getQuantifierBlocks());
			final Term resultTerm = qsForResult.toTerm();
			return new EliminationResult(res.getEliminationTask().update(resultTerm), res.getNewEliminatees());
		}
	}

	private EliminationResult tryToEliminateOne3(final EliminationTask inputEt) {
		final EliminationTaskPlain res = tryToEliminate(inputEt.getQuantifier(), inputEt.getTerm(),
				inputEt.getContext(), inputEt.getEliminatees().iterator().next());
		if (res == null) {
			return null;
		} else {
			final Set<TermVariable> newEliminatees = new HashSet<TermVariable>(res.getEliminatees());
			newEliminatees.removeAll(inputEt.getEliminatees());
			return new EliminationResult(new EliminationTask(res.getQuantifier(), inputEt.getEliminatees(),
					res.getTerm(), inputEt.getContext()), newEliminatees);
		}
	}

	private EliminationTaskPlain tryToEliminate(final int quantifier, final Term term, final Context context,
			final TermVariable eliminatee) {
		final EliminationTaskPlain inputEtp = new EliminationTaskPlain(quantifier, Collections.singleton(eliminatee),
				term, context.getCriticalConstraint());
		EliminationTaskPlain res1;
		try {
			res1 = ElimStorePlain.applyComplexEliminationRules(mServices, mLogger, mMgdScript, inputEtp);
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
		if (res1 != null) {
			if (Arrays.asList(res1.getTerm().getFreeVars()).contains(eliminatee)) {
				throw new AssertionError("Var not eliminated: " + eliminatee + " " + inputEtp.toTerm(mScript));
			}
		}
		return res1;
	}

}
