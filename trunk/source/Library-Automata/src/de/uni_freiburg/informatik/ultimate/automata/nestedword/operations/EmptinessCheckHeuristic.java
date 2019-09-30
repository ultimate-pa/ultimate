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

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SMTFeatureExtractionTermClassifier;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;

public class EmptinessCheckHeuristic<STATE, LETTER> implements IHeuristic<STATE, LETTER> {

	public enum ScoringMethod {
		NUM_FUNCTIONS,
		NUM_VARIABLES,
		DAGSIZE,
		DEPENDENCY
	}

	private final ILogger mLogger;
	private final SMTFeatureExtractionTermClassifier mTermClassifier;
	private final HashMap<LETTER, Integer> mCheckedTransitions;
	private final ScoringMethod mScoringMethod;

	public EmptinessCheckHeuristic(final ILogger logger, final ScoringMethod scoringMethod){
		mLogger = logger;
		mTermClassifier = new SMTFeatureExtractionTermClassifier(mLogger);
		mCheckedTransitions = new HashMap<>();
		mScoringMethod = scoringMethod;
	}

	public void checkTransition(final LETTER trans) {
		if(trans instanceof StatementSequence) {
			final UnmodifiableTransFormula transformula = ((StatementSequence) trans).getTransformula();
			final Term formula = transformula.getFormula();
			mTermClassifier.checkTerm(formula);
			int score = 0;
			if (mScoringMethod == ScoringMethod.DEPENDENCY) {
				score = mTermClassifier.getDependencyScore();
			}else if (mScoringMethod == ScoringMethod.NUM_FUNCTIONS) {
				score = mTermClassifier.getNumberOfFunctions();
			}else if (mScoringMethod == ScoringMethod.NUM_VARIABLES) {
				score = mTermClassifier.getNumberOfVariables();
			}else if (mScoringMethod == ScoringMethod.DAGSIZE) {
				score = mTermClassifier.getDAGSize();
			} else {
				throw new UnsupportedOperationException("Unsupported ScoringMethod " + mScoringMethod.toString());
			}
			mCheckedTransitions.put(trans, score);
		} else {
			throw new UnsupportedOperationException("Currently this function only supports transitions of type 'StatementSequence'. The passed transition has type: " + trans.getClass().getCanonicalName());
		}
	}

	@Override
	public int getHeuristicValue(final STATE state, final STATE stateK, final LETTER trans) {
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
}
