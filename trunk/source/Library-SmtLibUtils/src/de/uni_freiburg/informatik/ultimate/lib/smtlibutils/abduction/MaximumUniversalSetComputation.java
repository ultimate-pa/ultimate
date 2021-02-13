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
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.function.ToIntFunction;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class MaximumUniversalSetComputation {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mMgdScript;

	private final ToIntFunction<TermVariable> mCost;
	private final Term mContext;

	private Set<TermVariable> mPartialMus;
	private Term mQuantifiedMusFormula;
	private int mMusCost;

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

	public Set<TermVariable> getVariables() {
		return mPartialMus;
	}

	public Term getQuantifiedFormula() {
		return mQuantifiedMusFormula;
	}

	public int getCost() {
		return mMusCost;
	}

	private void computeMUS(final Term phi, final TermVariable[] variables, final int minVar, final int varCost,
			int lowerBound) {
		if (minVar >= variables.length || varCost <= lowerBound) {
			// No more variables, or bound cannot be improved.
			mPartialMus = new HashSet<>();
			mQuantifiedMusFormula = phi;
			mMusCost = 0;
			return;
		}

		// Initialization: assume no variables in MUS, no additional quantification of formula
		Set<TermVariable> bestMUS = new HashSet<>();
		Term bestFormula = phi;
		int bestCost = 0;

		// Pick variable x, and determine if x can be added to a universal set
		final TermVariable x = variables[minVar];
		final int xCost = mCost.applyAsInt(x);
		final Term quantifiedPhi = tryEliminateUniversal(x, phi);
		final LBool includeX = SmtUtils.checkSatTerm(mMgdScript.getScript(),
				SmtUtils.and(mMgdScript.getScript(), mContext, quantifiedPhi));

		if (includeX == LBool.SAT) {
			// If x can be added, compute remaining MUS after adding x
			computeMUS(quantifiedPhi, variables, minVar + 1, varCost - xCost, lowerBound - xCost);
			if (mMusCost + xCost > lowerBound) {
				bestMUS = mPartialMus;
				bestMUS.add(x);
				bestFormula = mQuantifiedMusFormula;
				bestCost = mMusCost + xCost;
				lowerBound = bestCost;
			}
		}

		// In either case, compute MUS without x
		computeMUS(phi, variables, minVar + 1, varCost - xCost, lowerBound);
		if (mMusCost > lowerBound) {
			bestMUS = mPartialMus;
			bestFormula = mQuantifiedMusFormula;
			bestCost = mMusCost;
		}

		// Determine result
		mPartialMus = bestMUS;
		mQuantifiedMusFormula = bestFormula;
		mMusCost = bestCost;
	}

	private Term tryEliminateUniversal(final TermVariable x, final Term phi) {
		final Term letFree = new FormulaUnLet().transform(phi);
		return PartialQuantifierElimination.quantifier(mServices, mLogger, mMgdScript,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION,
				QuantifiedFormula.FORALL, Collections.singleton(x), letFree);
	}
}
