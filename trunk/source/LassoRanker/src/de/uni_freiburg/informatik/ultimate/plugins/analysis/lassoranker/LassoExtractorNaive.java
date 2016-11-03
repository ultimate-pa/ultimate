/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE LassoRanker plug-in.
 * 
 * The ULTIMATE LassoRanker plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE LassoRanker plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE LassoRanker plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

/**
 * Naive algorithm to extract a stem and loop transition from a lasso program 
 * provided as RCFG with rootNode.
 * @author Matthias Heizmann
 */
@Deprecated
public class LassoExtractorNaive extends AbstractLassoExtractor {

	public LassoExtractorNaive(RootNode rootNode) {
		final List<IcfgLocation> rootSucc = rootNode.getOutgoingNodes();
		BoogieIcfgLocation firstNode = null;
		boolean programStemsFromCacslTranslation = false;
		boolean atLeastOneInappropriateSuccessor = false;
		int i = 0;
		for (final IcfgLocation succ : rootSucc) {
			final BoogieIcfgLocation pp = (BoogieIcfgLocation) succ;
			if (isProgramPointOfInitProcedure(pp)) {
				programStemsFromCacslTranslation = true;
			} else if (isProgramPointOfStartProcedure(pp)) {
				programStemsFromCacslTranslation = true;
			} else if (firstNode == null) {
				firstNode = pp;
			} else {
				atLeastOneInappropriateSuccessor = true;
			}
			i++;
		}
		assert (i<=3 || atLeastOneInappropriateSuccessor);
		if (atLeastOneInappropriateSuccessor) {
			mStem = null;
			mLoop = null;
			mHonda = null;
			mLassoFound = false;
			mSomeNoneForErrorReport = firstNode;
			return;
		}
		if (firstNode == null) {
			mStem = null;
			mLoop = null;
			mHonda = null;
			mLassoFound = false;
			mSomeNoneForErrorReport = rootNode;
			return;
		}
		final List<IcfgEdge> firstSucc = firstNode.getOutgoingEdges();
		if (firstSucc.size() == 1) {
			// this edge be the stem, the next node must be the honda
			final CodeBlock stemCodeBlock = (CodeBlock) firstSucc.get(0);
			mHonda = (BoogieIcfgLocation) stemCodeBlock.getTarget();
			mStem = constructNestedWordOfLenthOne(stemCodeBlock);
		} else if (firstSucc.size() == 2) {
			// there is no stem, this must already be the honda
			mStem = null;
			mHonda = firstNode;
		} else {
			mStem = null;
			mLoop = null;
			mHonda = null;
			mLassoFound = false;
			mSomeNoneForErrorReport = firstNode;
			return;
		}
		final List<IcfgEdge> hondaSuccs = mHonda.getOutgoingEdges();
		if (hondaSuccs.size() != 2) {
			// honda has to have two outgoing edges (one where the while loop
			// was taken, one where is is not taken)
			mLassoFound = false;
			mSomeNoneForErrorReport = mHonda;
			mLoop = null;
			return;
		}
		final CodeBlock hondaSucc0 = (CodeBlock) hondaSuccs.get(0);
		final CodeBlock hondaSucc1 = (CodeBlock) hondaSuccs.get(1);
		
		CodeBlock loopCand0 = checkForOneStepLoop(mHonda, hondaSucc0);
		CodeBlock loopCand1 = checkForOneStepLoop(mHonda, hondaSucc1);
		if (loopCand0 != null & loopCand1 != null) {
			// double loop
			mLassoFound = false;
			mSomeNoneForErrorReport = mHonda;
			mLoop = null;
		} else if (loopCand0 != null) {
			mLassoFound = true;
			mSomeNoneForErrorReport = null;
			mLoop = constructNestedWordOfLenthOne(loopCand0);
		} else if (loopCand1 != null) {
			mLassoFound = true;
			mSomeNoneForErrorReport = null;
			mLoop = constructNestedWordOfLenthOne(loopCand1);
		} else {
			// now, check for two step loop
			loopCand0 = checkForTwoStepLoop(mHonda, hondaSucc0);
			loopCand1 = checkForTwoStepLoop(mHonda, hondaSucc1);
			if (loopCand0 != null & loopCand1 != null) {
				// double loop
				mLassoFound = false;
				mSomeNoneForErrorReport = mHonda;
				mLoop = null;
			} else if (loopCand0 != null) {
				mLassoFound = true;
				mSomeNoneForErrorReport = null;
				mLoop = constructNestedWordOfLenthOne(loopCand0);
				assert programStemsFromCacslTranslation;
			} else if (loopCand1 != null) {
				mLassoFound = true;
				mSomeNoneForErrorReport = null;
				mLoop = constructNestedWordOfLenthOne(loopCand1);
				assert programStemsFromCacslTranslation;
			} else {
				mLassoFound = false;
				mSomeNoneForErrorReport = mHonda;
				mLoop = null;
			}
		}
	}
	
	/**
	 * Check if the ProgramPoints procedure is "ULTIMATE.init" which is an
	 * auxiliary procedure used in our CACSLTranslation.
	 */
	private boolean isProgramPointOfInitProcedure(BoogieIcfgLocation pp) {
		return pp.getProcedure().equals("ULTIMATE.init");
	}

	/**
	 * Check if the ProgramPoints procedure is "ULTIMATE.start" which is an
	 * auxiliary procedure used in our CACSLTranslation.
	 */
	private boolean isProgramPointOfStartProcedure(BoogieIcfgLocation pp) {
		return pp.getProcedure().equals("ULTIMATE.start");
	}
	
	private CodeBlock checkForOneStepLoop(BoogieIcfgLocation honda, CodeBlock hondaSucc) {
		if (hondaSucc.getTarget() == honda) {
			return hondaSucc;
		} else {
			return null;
		}
	}
	
	/**
	 * If the large block encoding of the RCFGBuilder the loop is represented by
	 * two successive edges. The first one has transition relation "true", the
	 * second one is the one we use as loop edge.
	 */
	private CodeBlock checkForTwoStepLoop(BoogieIcfgLocation honda, CodeBlock hondaSucc) {
		final CodeBlock loopEdge;
		final BoogieIcfgLocation interposition = (BoogieIcfgLocation) hondaSucc.getTarget();
		final List<IcfgEdge> interpositionSuccs = interposition.getOutgoingEdges();
		if (interpositionSuccs.size() != 2) {
			loopEdge = null;
		} else {
			final CodeBlock interpositionSucc0 = checkForOneStepLoop(honda, 
					(CodeBlock) interpositionSuccs.get(0));
			final CodeBlock interpositionSucc1 = checkForOneStepLoop(honda, 
					(CodeBlock) interpositionSuccs.get(1));
			if (interpositionSucc0 != null & interpositionSucc1 != null) {
				// double loop
				return null;
			} else if (interpositionSucc0 != null) {
				checkThatFormulaIsTrue(hondaSucc);
				loopEdge = interpositionSucc0;
			} else if (interpositionSucc1 != null) {
				checkThatFormulaIsTrue(hondaSucc);
				loopEdge = interpositionSucc1;
			} else {
				return null;
			}
		}
		return loopEdge;
	}

	/**
	 * Throw exception if formula of CodeBlock is not "true"
	 */
	private void checkThatFormulaIsTrue(CodeBlock cb) {
		final Term formula = cb.getTransitionFormula().getFormula();
		if (!formula.toString().equals("true")) {
			throw new UnsupportedOperationException(
									"unexpected loop representation");
		}
	}
	
	NestedWord<CodeBlock> constructNestedWordOfLenthOne(CodeBlock cb) {
		return new NestedWord<CodeBlock>(cb, NestedWord.INTERNAL_POSITION);
	}
}
