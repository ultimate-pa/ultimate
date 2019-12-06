/*
 * Copyright (C) 2019 Julian Löffler (loefflju@informatik.uni-freiburg.de), Breee@github
 * Copyright (C) 2012-2019 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SMTFeature;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SMTFeatureExtractionTermClassifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SMTFeatureExtractionTermClassifier.ScoringMethod;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SMTFeatureExtractor;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;

public class EmptinessCheckHeuristic<STATE, LETTER> implements IHeuristic<STATE, LETTER> {

	private final ILogger mLogger;
	private final HashMap<LETTER, Double> mCheckedTransitions;
	private final ScoringMethod mScoringMethod;
	private final SMTFeatureExtractor mFeatureExtractor;

	public EmptinessCheckHeuristic(final ILogger logger, final ScoringMethod scoringMethod) {
		mLogger = logger;
		mCheckedTransitions = new HashMap<>();
		mScoringMethod = scoringMethod;
		mFeatureExtractor = new SMTFeatureExtractor(logger, null, false);
	}

	public void checkTransition(final LETTER trans) {
		final SMTFeatureExtractionTermClassifier tc = new SMTFeatureExtractionTermClassifier(mLogger);
		UnmodifiableTransFormula transformula = null;
		if (trans instanceof StatementSequence) {
			transformula = ((StatementSequence) trans).getTransformula();
		} else if (trans instanceof SequentialComposition) {
			transformula = ((SequentialComposition) trans).getTransformula();
		} else {
			throw new UnsupportedOperationException(
					"Currently this function only supports transitions of type 'StatementSequence' or 'SequentialComposition'. The passed transition has type: "
							+ trans.getClass().getCanonicalName());
		}

		final Term formula = transformula.getFormula();
		tc.checkTerm(formula);
		final double score = tc.get_score(mScoringMethod);
		mCheckedTransitions.put(trans, score);
	}

	public ScoringMethod getScoringMethod() {
		return mScoringMethod;
	}

	@Override
	public double getHeuristicValue(final STATE state, final STATE stateK, final LETTER trans) {
		if (!mCheckedTransitions.containsKey(trans)) {
			checkTransition(trans);
		}
		return mCheckedTransitions.get(trans);
	}

	@Override
	public int getConcreteCost(final LETTER trans) {
		// TODO Auto-generated method stub
		return 1;
	}

	@Override
	public Map<IsEmptyHeuristic<LETTER, STATE>.Item, Integer> compareSuccessors(final List<IsEmptyHeuristic<LETTER, STATE>.Item> successors) {
		final Map<IsEmptyHeuristic<LETTER, STATE>.Item, Integer> successorToLosses = new HashMap<>();
		final Map<SMTFeature,IsEmptyHeuristic<LETTER, STATE>.Item> featureToSuccessor = new HashMap<>();
		if(successors.size() == 1) {
			successorToLosses.put(successors.get(0), 1);
			return successorToLosses;
		}
		successors.forEach(e -> {
			final LETTER trans = e.getTransition();
			UnmodifiableTransFormula transformula = null;
			if (trans instanceof StatementSequence) {
				transformula = ((StatementSequence) trans).getTransformula();
			} else if (trans instanceof SequentialComposition) {
				transformula = ((SequentialComposition) trans).getTransformula();
			} else {
				throw new UnsupportedOperationException(
						"Currently this function only supports transitions of type 'StatementSequence' or 'SequentialComposition'. The passed transition has type: "
								+ trans.getClass().getCanonicalName());
			}
			featureToSuccessor.put(mFeatureExtractor.extractFeatureRaw(transformula.getFormula()),e);
		});
		for (final Entry<SMTFeature, IsEmptyHeuristic<LETTER, STATE>.Item> entry1 : featureToSuccessor.entrySet()) {
			final SMTFeature feature1 = entry1.getKey();
			for (final Entry<SMTFeature, IsEmptyHeuristic<LETTER, STATE>.Item> entry2 : featureToSuccessor.entrySet()) {
				final SMTFeature feature2 = entry2.getKey();
				if(feature1 == feature2) {
					// do nothing
				}else{
					final SMTFeature looser = SMTFeature.chooseLooser(feature1,feature2);
					final IsEmptyHeuristic<LETTER, STATE>.Item successor  = featureToSuccessor.get(looser);
					final int curr_score = successorToLosses.getOrDefault(looser, 0) + 1;
					successorToLosses.put(successor, curr_score);
				}
			}
		}
		return successorToLosses;
	}
}
