package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker.TraceCheckerBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.util.RelationWithTreeSet;

/**
 * This class implements the possibility to partially annotate and assert the statements of a trace in order
 * to get better interpolants.
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class AnnotateAndAsserterWithStmtOrderPrioritization extends AnnotateAndAsserter {
	
//	TODO: Document heuristics
	/**
	 * 1. Heuristic:
	 */
	private static boolean m_Heuristic_1 = !true;
	
	/**
	 * 2. Heuristic: 
	 */
	private static boolean m_Heuristic_2 = !true;

	/**
	 * 3. Heuristic: ..
	 */
	private static boolean m_Heuristic_3 = true;
	
	public AnnotateAndAsserterWithStmtOrderPrioritization(
			SmtManager smtManager, NestedFormulas<Term, Term> nestedSSA,
			AnnotateAndAssertCodeBlocks aaacb, 
			TraceCheckerBenchmarkGenerator tcbg, Logger logger) {
		super(smtManager, nestedSSA, aaacb, tcbg,logger);
	}

	/**
	 *  Returns a set of integer where each integer <i>i</i> corresponds to a statement <i>i</i> of the given trace, such that:
	 *  <ul>
	 *  <li> every integer <i>i</i>: <i>i</i> < l_1 or <i>i</i> >= l_2 
	 *  <li> l_1: the lowest index of a program point p, such that p occurs at least twice, and l_1 >= lowerIndex
	 *  <li> l_2: the greatest index of the same program point p, such that l_2 <= upperIndex
	 *  </ul>
	**/
	@SuppressWarnings("unused")
	private Set<Integer> getSubTrace(NestedWord<CodeBlock> trace, int lowerIndex, int upperIndex) {
		assert lowerIndex >= 0 : "Lower index is negative";
		assert upperIndex > lowerIndex : "Upper index is <= lower index";
		assert upperIndex <= trace.length() : "Upper index is out of range";
		List<ProgramPoint> pps = TraceCheckerUtils.getSequenceOfProgramPoints(trace);
		RelationWithTreeSet<ProgramPoint, Integer> rwt = new RelationWithTreeSet<ProgramPoint, Integer>();
		for (int i = lowerIndex; i <= upperIndex; i++) {
			rwt.addPair(pps.get(i), i);
		}
		
		int lowestIndexOfPPThatOccursTwice = 0;
		int greatestIndexOfPPThatOccursTwice = trace.length();
		boolean existsPPThatOccursMoreThanOnce = false;
		for (int i = lowerIndex; i <= upperIndex; i++) {
			if (rwt.getImage(pps.get(i)).size() > 1) {
				// Get the first occurrence in the trace of that program-point, that occurs more than one time
				lowestIndexOfPPThatOccursTwice = ((TreeSet<Integer>) rwt.getImage(pps.get(i))).first();
				// Get the last occurrence of that program-point
				greatestIndexOfPPThatOccursTwice = ((TreeSet<Integer>) rwt.getImage(pps.get(i))).last();
				existsPPThatOccursMoreThanOnce = true;
				break;
			}
		}
		
		if (!existsPPThatOccursMoreThanOnce) {
			// If every program point occurs only once (no loops in the trace),
			// then return the set of integers {i | 0 <= i < trace.length}
			Set<Integer> allStmts = new HashSet<Integer>();
			for (int i = 0; i <  trace.length(); i++) {
				allStmts.add(i);
			}
			return allStmts;
		} else {
			// If there is a program point with more than one occurrences, then
			// put every statement before the index of the first occurrence and every statement 
			// after the index of the last occurrence into the set to be returned
			Set<Integer> stmtsWithOutLoop = new HashSet<Integer>();
			for (int i = lowerIndex; i < upperIndex; i++) {
				// Since a program-point represents the source node of a stmt, we have to
				// take here also greatestIndexOfPPThatOccursTwice-th element into our set stmtsWithOutLoop
				// that's why we have (i >= greatestIndexOfPPThatOccursTwice)
				if (i < lowestIndexOfPPThatOccursTwice || i >= greatestIndexOfPPThatOccursTwice) {
					stmtsWithOutLoop.add(i);
				}
			}
			return stmtsWithOutLoop;
		}
	}

	
	/**
	 * Returns the positions of program-points, which are equal to each other. (E.g. Program point x occurs at positions
	 * 1, 3, 9, then a treeset containing those values is returned.) 
	 * It considers the trace only at the interval [lowerIndex, upperIndex].
	 * @param trace
	 * @param lowerIndex
	 * @param upperIndex
	 * @return
	 */
	private TreeSet<Integer> getPositionsOfLoopStatements(NestedWord<CodeBlock> trace, int lowerIndex, int upperIndex) {
		assert lowerIndex >= 0 : "Lower index is negative";
		assert upperIndex > lowerIndex : "Upper index is <= lower index";
		assert upperIndex <= trace.length() : "Upper index is out of range";
		List<ProgramPoint> pps = TraceCheckerUtils.getSequenceOfProgramPoints(trace);
		RelationWithTreeSet<ProgramPoint, Integer> rwt = new RelationWithTreeSet<ProgramPoint, Integer>();
		for (int i = lowerIndex; i <= upperIndex; i++) {
			rwt.addPair(pps.get(i), i);
		}
		
		for (int i = lowerIndex; i <= upperIndex; i++) {
			if (rwt.getImage(pps.get(i)).size() > 1) {
				return (TreeSet<Integer>) rwt.getImage(pps.get(i));
			}
		}
		return new TreeSet<Integer>();
	}
	
	private Map.Entry<Integer, Integer> getIndicesOfProgramPointThatOccursTwice(NestedWord<CodeBlock> trace, int lowerIndex, int upperIndex) {
		assert lowerIndex >= 0 : "Lower index is negative";
		assert upperIndex <= trace.length() : "Upper index is out of range";
		
		if (upperIndex < lowerIndex) {
			return new AbstractMap.SimpleEntry<Integer, Integer>(upperIndex, upperIndex);
		}
		List<ProgramPoint> pps = TraceCheckerUtils.getSequenceOfProgramPoints(trace);
		RelationWithTreeSet<ProgramPoint, Integer> rwt = new RelationWithTreeSet<ProgramPoint, Integer>();
		for (int i = lowerIndex; i <= upperIndex; i++) {
			rwt.addPair(pps.get(i), i);
		}
		
		int lowestIndexOfPPThatOccursTwice = lowerIndex;
		int greatestIndexOfPPThatOccursTwice = upperIndex;
		for (int i = lowerIndex; i <= upperIndex; i++) {
			if (rwt.getImage(pps.get(i)).size() > 1) {
				// Get the first occurrence in the trace of that program-point, that occurs more than one time
				lowestIndexOfPPThatOccursTwice = ((TreeSet<Integer>) rwt.getImage(pps.get(i))).first();
				// Get the last occurrence of that program-point
				greatestIndexOfPPThatOccursTwice = ((TreeSet<Integer>) rwt.getImage(pps.get(i))).last();
				break;
			}
		}
		return new AbstractMap.SimpleEntry<Integer, Integer>(lowestIndexOfPPThatOccursTwice, greatestIndexOfPPThatOccursTwice);
	}
	
	

	
	
	
	private Set<Integer> getSetOfIntegerForGivenInterval(int lowerBound, int upperBound) {
		Set<Integer> result = new HashSet<Integer>();
		for (int i = lowerBound; i < upperBound; i++) {
			result.add(i);
		}
		return result;
	}
	
	
	private Set<Integer> integerSetDifference(Set<Integer> firstSet, Set<Integer> secondSet) {
		if (secondSet.isEmpty()) return firstSet;
		
		Set<Integer> result = new HashSet<Integer>();
		for (Integer i : firstSet) {
			if (!secondSet.contains(i)) {
				result.add(i);
			}
		}
		return result;
	}
	
	/**
	 * Returns (n-1) partitions, such that every partition covers a closed interval from [statements[i], statements[i+1]].  
	 */
	private List<Map.Entry<Integer, Integer>> getPartitionsOfStatements(List<Integer> statements) {
		List<Map.Entry<Integer, Integer>> result = new ArrayList<Map.Entry<Integer, Integer>>();
		for (int i = 0; i < statements.size() - 1; i++) {
			result.add(new AbstractMap.SimpleEntry<Integer, Integer>(statements.get(i), statements.get(i+1)));
		}
		return result;
	}
	
	@Override
	public void buildAnnotatedSsaAndAssertTerms() {
		
		Map.Entry<Integer, Integer> indicesOfStmtThatOccursTwice = getIndicesOfProgramPointThatOccursTwice(m_Trace, 0, m_Trace.length());
		int lowerIndexOfStmtThatOccursTwice = indicesOfStmtThatOccursTwice.getKey();
		int upperIndexOfStmtThatOccursTwice =  indicesOfStmtThatOccursTwice.getValue();
		
		Set<Integer> stmtsWithinLoop = getSetOfIntegerForGivenInterval(lowerIndexOfStmtThatOccursTwice, upperIndexOfStmtThatOccursTwice);
		Set<Integer> integersFromTrace = getSetOfIntegerForGivenInterval(0, m_Trace.length());
		Set<Integer> stmtsOutsideOfLoop = integerSetDifference(integersFromTrace, stmtsWithinLoop);
		
		m_AnnotSSA = new ModifiableNestedFormulas<Term, Term>(m_Trace, new TreeMap<Integer, Term>());
		
		m_AnnotSSA.setPrecondition(m_AnnotateAndAssertCodeBlocks.annotateAndAssertPrecondition());
		m_AnnotSSA.setPostcondition(m_AnnotateAndAssertCodeBlocks.annotateAndAssertPostcondition());
		Collection<Integer> callPositions = new ArrayList<Integer>();
		Collection<Integer> pendingReturnPositions = new ArrayList<Integer>();
		// Report benchmark
		m_Tcbg.reportnewCodeBlocks(m_Trace.length());
		// Apply 1. heuristic
		if (m_Heuristic_1) {
			// First, annotate and assert the statements, which doesn't occur within a loop
			buildAnnotatedSsaAndAssertTermsWithPriorizedOrder(m_Trace, callPositions, pendingReturnPositions, stmtsOutsideOfLoop);

			m_Satisfiable = m_SmtManager.getScript().checkSat();
			// Report benchmarks
			m_Tcbg.reportnewCheckSat();
			m_Tcbg.reportnewAssertedCodeBlocks(stmtsOutsideOfLoop.size());
			// If the statements outside of a loop are not unsatisfiable, then annotate and assert also
			// the rest of the statements
			if (m_Satisfiable != LBool.UNSAT && stmtsOutsideOfLoop.size() != m_Trace.length()) {
				buildAnnotatedSsaAndAssertTermsWithPriorizedOrder(m_Trace, callPositions, pendingReturnPositions, stmtsWithinLoop);
				assert callPositions.containsAll(m_Trace.getCallPositions());
				assert m_Trace.getCallPositions().containsAll(callPositions);
				m_Satisfiable = m_SmtManager.getScript().checkSat();
				// Report benchmarks
				m_Tcbg.reportnewCheckSat();
				m_Tcbg.reportnewAssertedCodeBlocks(stmtsWithinLoop.size());
			}
		} 
		// Apply 2. heuristic
		else if (m_Heuristic_2) {
			m_Satisfiable = LBool.UNKNOWN;
			Set<Integer> stmtsAlreadyAsserted = stmtsOutsideOfLoop;
			
			while (m_Satisfiable != LBool.UNSAT) {
				// First, annotate and assert the statements, which doesn't occur within a loop
				buildAnnotatedSsaAndAssertTermsWithPriorizedOrder(m_Trace, callPositions, pendingReturnPositions, stmtsOutsideOfLoop);
				m_Satisfiable = m_SmtManager.getScript().checkSat();
				// Report benchmarks
				m_Tcbg.reportnewCheckSat();
				m_Tcbg.reportnewAssertedCodeBlocks(stmtsOutsideOfLoop.size());
				
				if (stmtsAlreadyAsserted.size() == m_Trace.length()) break;
				if (m_Satisfiable != LBool.UNSAT) {
					// TODO: if lowerIndexOfStat.. + 1 > upperIndex - 1 --> then break, and add all the remaining statements
					indicesOfStmtThatOccursTwice = getIndicesOfProgramPointThatOccursTwice(m_Trace, lowerIndexOfStmtThatOccursTwice + 1, 
							upperIndexOfStmtThatOccursTwice-1);
					lowerIndexOfStmtThatOccursTwice = indicesOfStmtThatOccursTwice.getKey();
					upperIndexOfStmtThatOccursTwice =  indicesOfStmtThatOccursTwice.getValue();
					// update the set of statements which are already asserted
					Set<Integer> stmtsWithinLoopOld = stmtsWithinLoop; 
					stmtsWithinLoop = getSetOfIntegerForGivenInterval(lowerIndexOfStmtThatOccursTwice, upperIndexOfStmtThatOccursTwice);
					stmtsOutsideOfLoop = integerSetDifference(stmtsWithinLoopOld, stmtsWithinLoop);
					stmtsAlreadyAsserted.addAll(stmtsOutsideOfLoop);
				}
			}
		} 
		// Apply 3. heuristic
		else if (m_Heuristic_3) {
			TreeSet<Integer> loopProgramPoints = getPositionsOfLoopStatements(m_Trace, 0, m_Trace.length());
			m_Satisfiable = annotateAndAssertStmtsAccording3Heuristic(m_Trace, integersFromTrace, loopProgramPoints,
					callPositions,
					pendingReturnPositions);
		}
		mLogger.info("Conjunction of SSA is " + m_Satisfiable);
	}
	
	private LBool annotateAndAssertStmtsAccording3Heuristic(NestedWord<CodeBlock> trace,
			Set<Integer> unassertedStmts, TreeSet<Integer> loopProgramPoints,
			Collection<Integer> callPositions,
			Collection<Integer> pendingReturnPositions
			) {
		Set<Integer> stmtsWithinLoop = null;
		if (loopProgramPoints.isEmpty()) {
			stmtsWithinLoop = new HashSet<Integer>();
		} else {
			stmtsWithinLoop = getSetOfIntegerForGivenInterval(loopProgramPoints.first(), loopProgramPoints.last());
		}
		Set<Integer> stmtsOutsideOfLoop = integerSetDifference(unassertedStmts, stmtsWithinLoop);
		
		// Annotate and assert the statements which don't occur inside or in-between the @param loopProgramPoints 
		buildAnnotatedSsaAndAssertTermsWithPriorizedOrder(m_Trace, callPositions, pendingReturnPositions, stmtsOutsideOfLoop);
		LBool sat = m_SmtManager.getScript().checkSat();
		// Report benchmarks
		m_Tcbg.reportnewCheckSat();
		m_Tcbg.reportnewAssertedCodeBlocks(stmtsOutsideOfLoop.size());
		if (sat == LBool.UNSAT) {
			return sat;
		}
		List<Map.Entry<Integer, Integer>> parts = getPartitionsOfStatements(new ArrayList<Integer>(loopProgramPoints));
		// Treat every part of the partition as a loop, and call this method recursively with this part.
		for (Map.Entry<Integer, Integer> p : parts) {
			if (p.getKey() + 1 >= p.getValue() - 1) {
				loopProgramPoints = new TreeSet<Integer>();
			} else {
				loopProgramPoints = getPositionsOfLoopStatements(trace, p.getKey() + 1, p.getValue() - 1);
			}
			Set<Integer> stmtsWithinThisPart = getSetOfIntegerForGivenInterval(p.getKey(), p.getValue());
			sat = annotateAndAssertStmtsAccording3Heuristic(trace, stmtsWithinThisPart, loopProgramPoints, callPositions, pendingReturnPositions);
			if (sat == LBool.UNSAT) {
				return sat;
			}
		}
		return sat;
	}
	
	/**
	 * Annotate and assert every statement <i>i</i> from the given trace, such that
	 * <i>i</i> is an element of the given integer set stmtsToAssert.
	 */
	private void buildAnnotatedSsaAndAssertTermsWithPriorizedOrder(NestedWord<CodeBlock> trace, 
			Collection<Integer> callPositions,
			Collection<Integer> pendingReturnPositions,
			Set<Integer> stmtsToAssert) {
		for (Integer i : stmtsToAssert) {
			if (trace.isCallPosition(i)) {
				callPositions.add(i);
				m_AnnotSSA.setGlobalVarAssignmentAtPos(i, m_AnnotateAndAssertCodeBlocks.annotateAndAssertGlobalVarAssignemntCall(i));
				m_AnnotSSA.setLocalVarAssignmentAtPos(i, m_AnnotateAndAssertCodeBlocks.annotateAndAssertLocalVarAssignemntCall(i));
				m_AnnotSSA.setOldVarAssignmentAtPos(i, m_AnnotateAndAssertCodeBlocks.annotateAndAssertOldVarAssignemntCall(i));
			} else {
				if (trace.isReturnPosition(i) && trace.isPendingReturn(i)) {
					pendingReturnPositions.add(i);
				}
				m_AnnotSSA.setFormulaAtNonCallPos(i, m_AnnotateAndAssertCodeBlocks.annotateAndAssertNonCall(i));
			}
		}
		

		// number that the pending context. The first pending context has
		// number -1, the second -2, ...
		int pendingContextCode = -1 - m_SSA.getTrace().getPendingReturns().size();
		for (Integer positionOfPendingReturn : m_SSA.getTrace().getPendingReturns().keySet()) {
			assert trace.isPendingReturn(positionOfPendingReturn);
			{
				Term annotated = m_AnnotateAndAssertCodeBlocks.annotateAndAssertPendingContext(
						positionOfPendingReturn, pendingContextCode);
				m_AnnotSSA.setPendingContext(positionOfPendingReturn, annotated);
			}
			{
				Term annotated = m_AnnotateAndAssertCodeBlocks.annotateAndAssertLocalVarAssignemntPendingContext(
						positionOfPendingReturn, pendingContextCode);
				m_AnnotSSA.setLocalVarAssignmentAtPos(positionOfPendingReturn, annotated);
			}
			{
				Term annotated = m_AnnotateAndAssertCodeBlocks.annotateAndAssertOldVarAssignemntPendingContext(
						positionOfPendingReturn, pendingContextCode);
				m_AnnotSSA.setOldVarAssignmentAtPos(positionOfPendingReturn, annotated);
			}
			pendingContextCode++;
		}
	}
	
}
