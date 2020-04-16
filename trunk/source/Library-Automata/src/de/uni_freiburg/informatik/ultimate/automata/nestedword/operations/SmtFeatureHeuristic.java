/*
 * Copyright (C) 2019 Julian Löffler (loefflju@informatik.uni-freiburg.de), Breee@github
 * Copyright (C) 2019 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmptyHeuristic.IHeuristic;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SMTFeatureExtractionTermClassifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SMTFeatureExtractionTermClassifier.ScoringMethod;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class SmtFeatureHeuristic<STATE, LETTER> implements IHeuristic<STATE, LETTER> {

	private final ILogger mLogger;
	private final Map<LETTER, Double> mScoreCache;
	private final ScoringMethod mScoringMethod;

	public SmtFeatureHeuristic(final ILogger logger, final ScoringMethod scoringMethod) {
		if (scoringMethod == ScoringMethod.ZERO) {
			throw new IllegalArgumentException(
					"Zero scoring not supported; use zero heuristic from IHeuristic instead");
		}
		mLogger = logger;
		mScoreCache = new HashMap<>();
		mScoringMethod = scoringMethod;
	}

	public double checkTransition(final LETTER trans) {
		// Check transition formula using a TermClassifier, then assign a score
		// depending on the scoring method.

		if (trans instanceof IInternalAction) {
			final SMTFeatureExtractionTermClassifier tc = new SMTFeatureExtractionTermClassifier(mLogger);
			final Term formula = ((IInternalAction) trans).getTransformula().getFormula();
			tc.checkTerm(formula);
			return tc.getScore(mScoringMethod);
		} else if (trans instanceof ICallAction) {
			return 1.0;
		} else {
			return 0.5;
		}
	}

	@Override
	public double getHeuristicValue(final STATE state, final STATE stateK, final LETTER trans) {
		return mScoreCache.computeIfAbsent(trans, this::checkTransition);
	}

	@Override
	public double getConcreteCost(final LETTER trans) {
		// Our concrete const is 1, such that our heuristic always underestimates.
		return mScoreCache.computeIfAbsent(trans, this::checkTransition);
	}
}
