/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE SmtLibUtils Library.
 *
 * The ULTIMATE SmtLibUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SmtLibUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SmtLibUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SmtLibUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SmtLibUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.abduction;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;
import java.util.function.ToIntFunction;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Computes a maximum universal set for a given formula phi, i.e., a subset X of phi's free variables, such that
 * "\forall X. phi" is satisfiable, and such that X maximizes a cost function.
 *
 * Based on the paper "Minimum Satisfying Assignments for SMT" by Isil Dillig, Thomas Dillig, Kenneth L. McMillan and
 * Alex Aiken (CAV 2012).
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class MaximumUniversalSetComputation {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mMgdScript;

	private final ToIntFunction<TermVariable> mCost;
	private final Term mContext;

	private Set<TermVariable> mUniversalSet;
	private Term mQuantifiedUniversalFormula;
	private int mUniversalSetCost;

	/**
	 * Run a new maximum universal set computation.
	 *
	 * @param services
	 *            Ultimate services (for logging and quantifier elimination)
	 * @param mgdScript
	 *            A script that is used to check satisfiability, and for quantifier elimination
	 * @param phi
	 *            The formula whose maximum universal set is computed. Must be satisfiable.
	 * @param context
	 *            An optional context formula (set to null if not needed). If given, the universal set X that is
	 *            computed must be such that "context /\ \forall X. phi" is satisfiable.
	 * @param cost
	 *            A function that assigns a cost to each variable in the term. This will be maximized by the computed
	 *            universal set.
	 */
	public MaximumUniversalSetComputation(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final Term phi, final Term context, final ToIntFunction<TermVariable> cost) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(MaximumUniversalSetComputation.class);
		mMgdScript = mgdScript;
		mContext = context;
		mCost = cost;

		final TermVariable[] variables = phi.getFreeVars();
		final int varCost = Arrays.stream(variables).collect(Collectors.summingInt(mCost));
		computeMUS(phi, variables, 0, varCost, 0);
	}

	/**
	 * Get the variables in the universal set.
	 *
	 * @return the set X, as described above
	 */
	public Set<TermVariable> getVariables() {
		return mUniversalSet;
	}

	/**
	 * A satisfiable formula equivalent to "\forall X. phi". Simplification and partial quantifier elimination may have
	 * been applied.
	 *
	 * @return the universally-quantified input formula
	 */
	public Term getQuantifiedFormula() {
		return mQuantifiedUniversalFormula;
	}

	/**
	 * The cost of the computed maximum universal set.
	 *
	 * @return the sum of the cost of all variables in the set
	 */
	public int getCost() {
		return mUniversalSetCost;
	}

	private void computeMUS(final Term phi, final TermVariable[] variables, final int minVar, final int varCost,
			int lowerBound) {
		if (minVar >= variables.length || varCost <= lowerBound) {
			// No more variables, or bound cannot be improved.
			mUniversalSet = new HashSet<>();
			mQuantifiedUniversalFormula = phi;
			mUniversalSetCost = 0;
			return;
		}

		// Initialization: assume no variables in maximum universal set; no additional quantification of formula
		Set<TermVariable> bestUniversalSet = new HashSet<>();
		Term bestFormula = phi;
		int bestCost = 0;

		// Pick variable x, and determine if x can be added to a universal set
		final TermVariable x = variables[minVar];
		final int xCost = mCost.applyAsInt(x);
		final Term quantifiedPhi = tryEliminateUniversal(x, phi);
		final LBool includeX = SmtUtils.checkSatTerm(mMgdScript.getScript(), getWithContext(quantifiedPhi));

		if (includeX == LBool.SAT) {
			// If x can be added, compute remaining maximum universal set after adding x
			computeMUS(quantifiedPhi, variables, minVar + 1, varCost - xCost, lowerBound - xCost);
			if (mUniversalSetCost + xCost > lowerBound) {
				bestUniversalSet = mUniversalSet;
				bestUniversalSet.add(x);
				bestFormula = mQuantifiedUniversalFormula;
				bestCost = mUniversalSetCost + xCost;
				lowerBound = bestCost;
			}
		}

		// In either case, compute maximum universal set without x
		computeMUS(phi, variables, minVar + 1, varCost - xCost, lowerBound);
		if (mUniversalSetCost > lowerBound) {
			bestUniversalSet = mUniversalSet;
			bestFormula = mQuantifiedUniversalFormula;
			bestCost = mUniversalSetCost;
		}

		// Determine result
		mUniversalSet = bestUniversalSet;
		mQuantifiedUniversalFormula = bestFormula;
		mUniversalSetCost = bestCost;
	}

	private Term getWithContext(final Term formula) {
		if (mContext == null) {
			return formula;
		}
		return SmtUtils.and(mMgdScript.getScript(), mContext, formula);
	}

	private Term tryEliminateUniversal(final TermVariable x, final Term phi) {
		final Term letFree = new FormulaUnLet().transform(phi);
		return PartialQuantifierElimination.eliminate(mServices, mMgdScript,
				SmtUtils.quantifier(mMgdScript.getScript(), QuantifiedFormula.FORALL, Set.of(x), letFree),
				SimplificationTechnique.SIMPLIFY_DDA);
	}
}
