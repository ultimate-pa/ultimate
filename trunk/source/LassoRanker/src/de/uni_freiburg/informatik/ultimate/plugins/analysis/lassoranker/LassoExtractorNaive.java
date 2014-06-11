package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

/**
 * Naive algorithm to extract a stem and loop transition from a lasso program 
 * provided as RCFG with rootNode.
 * @author Matthias Heizmann
 */
@Deprecated
public class LassoExtractorNaive extends AbstractLassoExtractor {

	public LassoExtractorNaive(RootNode rootNode) {
		List<RCFGNode> rootSucc = rootNode.getOutgoingNodes();
		ProgramPoint firstNode = null;
		boolean programStemsFromCacslTranslation = false;
		boolean atLeastOneInappropriateSuccessor = false;
		int i = 0;
		for (RCFGNode succ : rootSucc) {
			ProgramPoint pp = (ProgramPoint) succ;
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
			m_Stem = null;
			m_Loop = null;
			m_Honda = null;
			m_LassoFound = false;
			m_SomeNoneForErrorReport = firstNode;
			return;
		}
		if (firstNode == null) {
			m_Stem = null;
			m_Loop = null;
			m_Honda = null;
			m_LassoFound = false;
			m_SomeNoneForErrorReport = rootNode;
			return;
		}
		List<RCFGEdge> firstSucc = firstNode.getOutgoingEdges();
		if (firstSucc.size() == 1) {
			// this edge be the stem, the next node must be the honda
			CodeBlock stemCodeBlock = (CodeBlock) firstSucc.get(0);
			m_Honda = (ProgramPoint) stemCodeBlock.getTarget();
			m_Stem = constructNestedWordOfLenthOne(stemCodeBlock);
		} else if (firstSucc.size() == 2) {
			// there is no stem, this must already be the honda
			m_Stem = null;
			m_Honda = firstNode;
		} else {
			m_Stem = null;
			m_Loop = null;
			m_Honda = null;
			m_LassoFound = false;
			m_SomeNoneForErrorReport = firstNode;
			return;
		}
		List<RCFGEdge> hondaSuccs = m_Honda.getOutgoingEdges();
		if (hondaSuccs.size() != 2) {
			// honda has to have two outgoing edges (one where the while loop
			// was taken, one where is is not taken)
			m_LassoFound = false;
			m_SomeNoneForErrorReport = m_Honda;
			m_Loop = null;
			return;
		}
		CodeBlock hondaSucc0 = (CodeBlock) hondaSuccs.get(0);
		CodeBlock hondaSucc1 = (CodeBlock) hondaSuccs.get(1);
		
		CodeBlock loopCand0 = checkForOneStepLoop(m_Honda, hondaSucc0);
		CodeBlock loopCand1 = checkForOneStepLoop(m_Honda, hondaSucc1);
		if (loopCand0 != null & loopCand1 != null) {
			// double loop
			m_LassoFound = false;
			m_SomeNoneForErrorReport = m_Honda;
			m_Loop = null;
		} else if (loopCand0 != null) {
			m_LassoFound = true;
			m_SomeNoneForErrorReport = null;
			m_Loop = constructNestedWordOfLenthOne(loopCand0);
		} else if (loopCand1 != null) {
			m_LassoFound = true;
			m_SomeNoneForErrorReport = null;
			m_Loop = constructNestedWordOfLenthOne(loopCand1);
		} else {
			// now, check for two step loop
			loopCand0 = checkForTwoStepLoop(m_Honda, hondaSucc0);
			loopCand1 = checkForTwoStepLoop(m_Honda, hondaSucc1);
			if (loopCand0 != null & loopCand1 != null) {
				// double loop
				m_LassoFound = false;
				m_SomeNoneForErrorReport = m_Honda;
				m_Loop = null;
			} else if (loopCand0 != null) {
				m_LassoFound = true;
				m_SomeNoneForErrorReport = null;
				m_Loop = constructNestedWordOfLenthOne(loopCand0);
				assert programStemsFromCacslTranslation;
			} else if (loopCand1 != null) {
				m_LassoFound = true;
				m_SomeNoneForErrorReport = null;
				m_Loop = constructNestedWordOfLenthOne(loopCand1);
				assert programStemsFromCacslTranslation;
			} else {
				m_LassoFound = false;
				m_SomeNoneForErrorReport = m_Honda;
				m_Loop = null;
			}
		}
	}
	
	/**
	 * Check if the ProgramPoints procedure is "ULTIMATE.init" which is an
	 * auxiliary procedure used in our CACSLTranslation.
	 */
	private boolean isProgramPointOfInitProcedure(ProgramPoint pp) {
		return pp.getProcedure().equals("ULTIMATE.init");
	}

	/**
	 * Check if the ProgramPoints procedure is "ULTIMATE.start" which is an
	 * auxiliary procedure used in our CACSLTranslation.
	 */
	private boolean isProgramPointOfStartProcedure(ProgramPoint pp) {
		return pp.getProcedure().equals("ULTIMATE.start");
	}
	
	private CodeBlock checkForOneStepLoop(ProgramPoint honda, CodeBlock hondaSucc) {
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
	private CodeBlock checkForTwoStepLoop(ProgramPoint honda, CodeBlock hondaSucc) {
		final CodeBlock loopEdge;
		ProgramPoint interposition = (ProgramPoint) hondaSucc.getTarget();
		List<RCFGEdge> interpositionSuccs = interposition.getOutgoingEdges();
		if (interpositionSuccs.size() != 2) {
			loopEdge = null;
		} else {
			CodeBlock interpositionSucc0 = checkForOneStepLoop(honda, 
					(CodeBlock) interpositionSuccs.get(0));
			CodeBlock interpositionSucc1 = checkForOneStepLoop(honda, 
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
		Term formula = cb.getTransitionFormula().getFormula();
		if (!formula.toString().equals("true")) {
			throw new UnsupportedOperationException(
									"unexpected loop representation");
		}
	}
	
	NestedWord<CodeBlock> constructNestedWordOfLenthOne(CodeBlock cb) {
		return new NestedWord<CodeBlock>(cb, NestedWord.INTERNAL_POSITION);
	}
}
