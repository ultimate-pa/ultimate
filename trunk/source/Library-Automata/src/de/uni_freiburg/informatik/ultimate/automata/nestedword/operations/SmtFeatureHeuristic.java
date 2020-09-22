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
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmptyHeuristic.IHeuristic;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SMTFeature;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SMTFeatureExtractionTermClassifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SMTFeatureExtractionTermClassifier.ScoringMethod;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SMTFeatureExtractor;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class SmtFeatureHeuristic<STATE, LETTER> implements IHeuristic<STATE, LETTER> {

	private Map<LETTER, Double> mScoreCache;
	private final ScoringMethod mScoringMethod;
	private final SMTFeatureExtractor mFeatureExtractor;

	public SmtFeatureHeuristic(final ScoringMethod scoringMethod) {
		mScoreCache = new HashMap<>();
		mScoringMethod = scoringMethod;
		mFeatureExtractor = new SMTFeatureExtractor(null, null, false);
	}

	public double checkTransition(final LETTER trans) {
		// Check transition formula using a TermClassifier, then assign a score
		// depending on the scoring method.

		if (trans instanceof IInternalAction) {
			final SMTFeatureExtractionTermClassifier tc = new SMTFeatureExtractionTermClassifier();
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
		return mScoreCache.computeIfAbsent(trans, this::checkTransition);
	}

	public void compareSuccessors(final List<IsEmptyHeuristic<LETTER, STATE>.Item> successors) {
		final Map<SMTFeature, LETTER> featureToSuccessor = new HashMap<>();

		mScoreCache.clear();

		if (successors.size() == 1) {
			mScoreCache.put(successors.iterator().next().getLetter(), 0.5);
			return;
		}

		// For each successor extract a SMTFeature
		successors.forEach(e -> {
			final LETTER trans = e.getLetter();
			UnmodifiableTransFormula transformula = null;
			// We only want to consider IAction's
			transformula = ((IAction) trans).getTransformula();
			featureToSuccessor.put(mFeatureExtractor.extractFeatureRaw(transformula.getFormula()), trans);
			// TODO: what happens with transitions, that are no IActions, can that even happen?
		});

		// Pairwise compare successors
		for (final Entry<SMTFeature, LETTER> entry1 : featureToSuccessor.entrySet()) {
			final SMTFeature feature1 = entry1.getKey();
			for (final Entry<SMTFeature, LETTER> entry2 : featureToSuccessor.entrySet()) {
				final SMTFeature feature2 = entry2.getKey();
				if (feature1 == feature2) {
					// do nothing
				} else {
					// We calculate which feature is worse and increase its number of losses.
					// In the end, the worst feature has the highest score.
					// TODO: Handle INTERNAL, CALL, RETURN separately.
					final SMTFeature looser = SMTFeature.chooseLooser(feature1, feature2);
					final LETTER looser_trans = featureToSuccessor.get(looser);
					final Double curr_looser_score = mScoreCache.getOrDefault(looser_trans, 0.5) + 1;
					mScoreCache.put(looser_trans, curr_looser_score);
					final LETTER winner_trans = looser != feature1 ? entry1.getValue() : entry2.getValue();
					if (!mScoreCache.containsKey(winner_trans)) {
						mScoreCache.put(winner_trans, 0.5);
					}
				}
			}
		}
		mScoreCache = mScoreCache.entrySet().stream().collect(Collectors.toMap(Entry::getKey,
				e -> SMTFeatureExtractionTermClassifier.normalize(e.getValue(), 0.5, 1.0)));
	}

	public ScoringMethod getScoringMethod() {
		return mScoringMethod;
	}
}
