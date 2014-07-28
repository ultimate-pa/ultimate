package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerUtils.InterpolantsPreconditionPostcondition;

/**
 * Object that will analyze a trace with respect to a sequence of ProgramPoints 
 * and a sequence of interpolants.
 * The analysis starts at the beginning of the trace. For each ProgramPoint
 * that has already appeared while traversing the trace we check if the
 * current interpolant implies the interpolant at the position of the recurring
 * ProgramPoint.
 * @author heizmann@informatik.uni-freiburg.de
 */
public class CoverageAnalysis {

	protected final Logger mLogger ;
	
	protected final NestedWord<CodeBlock> m_NestedWord;
	private List<ProgramPoint> m_ProgramPointSequence;
	private final IPredicate[] m_Interpolants;
	private final PredicateUnifier m_PredicateUnifier;
	
	private final Map<ProgramPoint, List<Integer>> m_ProgramPoint2Occurence = 
		new HashMap<ProgramPoint, List<Integer>>();
	
	private int m_Unsat;
	private int m_Sat;
	private int m_Unknown;
	private int m_Trivial;
	
	protected final TraceChecker m_TraceChecker;
	protected final InterpolantsPreconditionPostcondition m_IPP;

	public CoverageAnalysis(
			TraceChecker traceChecker,
			List<ProgramPoint> programPointSequence, Logger logger) {
		mLogger = logger;
		m_Interpolants = traceChecker.getInterpolants();
		m_NestedWord = NestedWord.nestedWord(traceChecker.getTrace());
		m_ProgramPointSequence = programPointSequence;
		m_PredicateUnifier = traceChecker.getPredicateUnifier();
		m_TraceChecker = traceChecker;
		m_IPP = new InterpolantsPreconditionPostcondition(traceChecker);
	}
	
	public void analyze() {
		assert(m_NestedWord.length()-1 == m_Interpolants.length);
		preprocess();
		
		for (int i=0; i<m_NestedWord.length(); i++) {

			processCodeBlock(i);

			ProgramPoint pp = m_ProgramPointSequence.get(i);
			List<Integer> previousOccurrences = m_ProgramPoint2Occurence.get(pp);
			if (previousOccurrences == null) {
				previousOccurrences = new ArrayList<Integer>();
				m_ProgramPoint2Occurence.put(pp, previousOccurrences);
			} else {
				for (int previousOccurrence : previousOccurrences) {
					assert i > previousOccurrence;
					IPredicate currentPredicate = m_IPP.getInterpolant(i);
					IPredicate previousPredicate = m_IPP.getInterpolant(previousOccurrence);
					if (currentPredicate == previousPredicate) {
						// trivially covered and backedges already contained
						m_Trivial++;
					} else {
						LBool lbool = m_PredicateUnifier.getCoverageRelation().isCovered(
								currentPredicate, previousPredicate);
						processCoveringResult(i, previousOccurrence, lbool);
						switch (lbool) {
						case UNSAT:
							m_Unsat++;
							break;
						case SAT:
							m_Sat++;
							break;
						case UNKNOWN:
							m_Unknown++;
							break;
						default:
							throw new AssertionError();
						}
					}
				}
			}
			previousOccurrences.add(i);
		}
		assert sumCountedOccurrences() == m_ProgramPointSequence.size() - 1;

		postprocess();
		
		mLogger.info("Checked inductivity of " +
				(m_Unsat+m_Sat+m_Unknown+m_Trivial) +	" backedges. " + 
				m_Unsat + " proven. " + 
				m_Sat + " refuted. " + 
				m_Unknown + " times theorem prover too weak." +
				m_Trivial + " trivial.");

	}

	private int sumCountedOccurrences() {
		int occurrenceSum = 0;
		for (Entry<ProgramPoint, List<Integer>> entry : m_ProgramPoint2Occurence.entrySet()) {
			occurrenceSum += entry.getValue().size();
		}
		return occurrenceSum;
	}

	protected void processCodeBlock(int i) {
		// do nothing
	}

	protected void processCoveringResult(int currentPosition,
			int previousOccurrence, LBool lbool) {
		// do nothing
	}

	protected void postprocess() {
		// do nothing
	}

	protected void preprocess() {
		// do nothing
	}
	
	
	public static List<ProgramPoint> extractProgramPoints(IRun<CodeBlock, IPredicate> irun) {
		ArrayList<IPredicate> predicateSequence = 
				((NestedRun<CodeBlock, IPredicate>) irun).getStateSequence();
		ArrayList<ProgramPoint> result = new ArrayList<>();
		for (IPredicate p : predicateSequence) {
			result.add(((ISLPredicate) p).getProgramPoint());
		}
		return result;
	}
	
	
	public BackwardCoveringInformation getBackwardCoveringInformation() {
		int potentialBackwardCoverings = (m_Unsat+m_Sat+m_Unknown+m_Trivial);
		int successfullBackwardCoverings = m_Unsat+m_Trivial;
		return new BackwardCoveringInformation(potentialBackwardCoverings, successfullBackwardCoverings);
	}
	
	
	public static class BackwardCoveringInformation {
		private int m_PotentialBackwardCoverings;
		private int m_SuccessfullBackwardCoverings;
		
		public BackwardCoveringInformation(int potentialBackwardCoverings,
				int successfullBackwardCoverings) {
			super();
			m_PotentialBackwardCoverings = potentialBackwardCoverings;
			m_SuccessfullBackwardCoverings = successfullBackwardCoverings;
		}
		
		public BackwardCoveringInformation(BackwardCoveringInformation bci1, BackwardCoveringInformation bci2) {
			m_PotentialBackwardCoverings = bci1.getPotentialBackwardCoverings() + bci2.getPotentialBackwardCoverings();
			m_SuccessfullBackwardCoverings = bci1.getSuccessfullBackwardCoverings() + bci2.getSuccessfullBackwardCoverings();
		}
		public int getPotentialBackwardCoverings() {
			return m_PotentialBackwardCoverings;
		}
		public int getSuccessfullBackwardCoverings() {
			return m_SuccessfullBackwardCoverings;
		}

		@Override
		public String toString() {
			return m_SuccessfullBackwardCoverings + "/" + m_PotentialBackwardCoverings;
//			if (m_PotentialBackwardCoverings == 0) {
//				return "not available";
//			} else {
//				long result = Math.round((((double) m_SuccessfullBackwardCoverings) / m_PotentialBackwardCoverings) * 100);
//				return result + "%";
//			}
		}
		
	}

}