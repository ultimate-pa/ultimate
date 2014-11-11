package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker.TraceCheckerBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.util.RelationWithTreeSet;

/**
 * This class implements the possibility to partially (and in different order) annotate and assert the statements of a trace in order
 * to get better interpolants.
 * 
 * Following heuristics are currently implemented:
 ********** 1. Heuristic ********* 
 * First, assert all statements which don't occur inside of a loop. Then, check for satisfiability. 
 * If the result of the satisfiability check is not unsatisfiable, then assert the rest of the statements, and return the 
 * result of the unsatisfiability check.
 
 ********* 2. Heuristic *********
 * Assert statements in incremental order by their depth, and check after each step for satisfiability. E.g. first assert all
 * statements with depth 0, then assert all statements at depth 1, and so on.
 * 
 ********* 3. Heuristic *********
 * TODO(Betim):
 ********* 4. Heuristic *********
 * The 4.th heuristic is a mix-up of the 2nd the 3rd heuristic.
 *    
 * @author musab@informatik.uni-freiburg.de
 */
public class AnnotateAndAsserterWithStmtOrderPrioritization extends AnnotateAndAsserter {

	private final AssertCodeBlockOrder m_AssertCodeBlocksOrder;
	
	public AnnotateAndAsserterWithStmtOrderPrioritization(
			SmtManager smtManager, NestedFormulas<Term, Term> nestedSSA,
			AnnotateAndAssertCodeBlocks aaacb, 
			TraceCheckerBenchmarkGenerator tcbg,
			AssertCodeBlockOrder assertCodeBlocksOrder, 
			Logger logger) {
		super(smtManager, nestedSSA, aaacb, tcbg,logger);
		m_AssertCodeBlocksOrder = assertCodeBlocksOrder;
	}

	/**
	 * Returns a set of integers containing the values {lowerBound, lowerBound + 1, ..., upperBound - 1}.
	 */
	private Set<Integer> getSetOfIntegerForGivenInterval(int lowerBound, int upperBound) {
		Set<Integer> result = new HashSet<Integer>();
		for (int i = lowerBound; i < upperBound; i++) {
			result.add(i);
		}
		return result;
	}
	
	
	/**
	 * Returns the set difference between first set and the second set.
	 */
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
	
	private void dfsPartitionStatementsAccordingToDepth(Integer lowerIndex,
			Integer upperIndex, int depth,
			RelationWithTreeSet<ProgramPoint, Integer> rwt,
			Map<Integer, Set<Integer>> depth2Statements, List<ProgramPoint> pps) {
		int i = lowerIndex;
		while (i < upperIndex) {
			// Is the current statement a loop entry?
			if (rwt.getImage(pps.get(i)).size() >= 2 &&
					((TreeSet<Integer>) rwt.getImage(pps.get(i))).higher(i) != null &&
					((TreeSet<Integer>) rwt.getImage(pps.get(i))).higher(i) < upperIndex) {
				int newUpperIndex = ((TreeSet<Integer>) rwt.getImage(pps.get(i))).higher(i);
				addStmtPositionToDepth(depth + 1, depth2Statements, i);
				// recursively partition the statements within this loop 
				dfsPartitionStatementsAccordingToDepth(i + 1, newUpperIndex, depth + 1,
						rwt, depth2Statements ,pps);
				// If there is no position greater than newUpperIndex, then the statement at position=newUpperIndex
				// is the loop exit
				if (((TreeSet<Integer>) rwt.getImage(pps.get(i))).higher(newUpperIndex) == null) {
					addStmtPositionToDepth(depth, depth2Statements, newUpperIndex);
					i = newUpperIndex + 1;
				} else { 
					// Otherwise the statement at position=newUpperIndex is a loop entry, which represents
					// another loop iteration
					i = newUpperIndex;	
				}
				
			} else {
				addStmtPositionToDepth(depth, depth2Statements, i);
				i++;
			}
		}
		
		
	}

	/**
	 * TODO:
	 */
	private void addStmtPositionToDepth(int depth,
			Map<Integer, Set<Integer>> depth2Statements, int stmtPos) {
		if (depth2Statements.keySet().contains(depth)) {
			depth2Statements.get(depth).add(stmtPos);
		} else {
			Set<Integer> s = new HashSet<Integer>();
			s.add(stmtPos);
			depth2Statements.put(depth, s);
		}
	}

	

	private Map<Integer, Set<Integer>> partitionStatementsAccordingDepth(NestedWord<CodeBlock> trace, RelationWithTreeSet<ProgramPoint, Integer> rwt,
			List<ProgramPoint> pps) {
		Map<Integer, Set<Integer>> depth2Statements = new HashMap<Integer, Set<Integer>>();
		
		dfsPartitionStatementsAccordingToDepth(0, trace.length(), 0, rwt, depth2Statements, pps);
		
		return depth2Statements;
		
	}
	
	@Override
	public void buildAnnotatedSsaAndAssertTerms() {
		List<ProgramPoint> pps = TraceCheckerUtils.getSequenceOfProgramPoints(m_Trace);
		RelationWithTreeSet<ProgramPoint, Integer> rwt = computeRelationWithTreeSetForTrace(0, m_Trace.length(), pps);
		
		Set<Integer> integersFromTrace = getSetOfIntegerForGivenInterval(0, m_Trace.length());
		m_AnnotSSA = new ModifiableNestedFormulas<Term, Term>(m_Trace, new TreeMap<Integer, Term>());
		
		m_AnnotSSA.setPrecondition(m_AnnotateAndAssertCodeBlocks.annotateAndAssertPrecondition());
		m_AnnotSSA.setPostcondition(m_AnnotateAndAssertCodeBlocks.annotateAndAssertPostcondition());
		Collection<Integer> callPositions = new ArrayList<Integer>();
		Collection<Integer> pendingReturnPositions = new ArrayList<Integer>();
		
		Map<Integer, Set<Integer>> depth2Statements = partitionStatementsAccordingDepth(m_Trace, rwt, pps);
		// Report benchmark
		m_Tcbg.reportnewCodeBlocks(m_Trace.length());
		// Apply 1. heuristic
		if (m_AssertCodeBlocksOrder == AssertCodeBlockOrder.OUTSIDE_LOOP_FIRST1) {
			// Statements outside of a loop have depth 0.
			Set<Integer> stmtsOutsideOfLoop = depth2Statements.get(0);
			// First, annotate and assert the statements, which doesn't occur within a loop
			buildAnnotatedSsaAndAssertTermsWithPriorizedOrder(m_Trace, callPositions, pendingReturnPositions, stmtsOutsideOfLoop);

			m_Satisfiable = m_SmtManager.getScript().checkSat();
			// Report benchmarks
			m_Tcbg.reportnewCheckSat();
			m_Tcbg.reportnewAssertedCodeBlocks(stmtsOutsideOfLoop.size());
			// If the statements outside of a loop are not unsatisfiable, then annotate and assert also
			// the rest of the statements
			if (m_Satisfiable != LBool.UNSAT && stmtsOutsideOfLoop.size() != m_Trace.length()) {
				Set<Integer> stmtsWithinLoop = integerSetDifference(integersFromTrace, stmtsOutsideOfLoop);
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
		else if (m_AssertCodeBlocksOrder == AssertCodeBlockOrder.OUTSIDE_LOOP_FIRST2) {
			m_Satisfiable = annotateAndAssertStmtsAccording2Heuristic(m_Trace, callPositions,
					pendingReturnPositions, depth2Statements);
		}// Apply 3. Heuristic
		else if (m_AssertCodeBlocksOrder == AssertCodeBlockOrder.INSIDE_LOOP_FIRST1) {
			m_Satisfiable = annotateAndAssertStmtsAccording3Heuristic(m_Trace, callPositions,
					pendingReturnPositions, depth2Statements);
		} // Apply 4. Heuristic
		else if (m_AssertCodeBlocksOrder == AssertCodeBlockOrder.MIX_INSIDE_OUTSIDE) {
			m_Satisfiable = annotateAndAssertStmtsAccording4Heuristic(m_Trace, callPositions,
					pendingReturnPositions, depth2Statements);
		} else {
			throw new AssertionError("unknown value " + m_AssertCodeBlocksOrder);
		}
		mLogger.info("Conjunction of SSA is " + m_Satisfiable);
	}

	private LBool annotateAndAssertStmtsAccording2Heuristic(NestedWord<CodeBlock> trace,
			Collection<Integer> callPositions,
			Collection<Integer> pendingReturnPositions,
			Map<Integer, Set<Integer>> depth2Statements
			) {
		List<Integer> keysInSortedOrder = new ArrayList<Integer>(depth2Statements.keySet()); 
		Collections.sort(keysInSortedOrder);
		LBool sat = null;
		for (Integer key : keysInSortedOrder) {
			buildAnnotatedSsaAndAssertTermsWithPriorizedOrder(trace, callPositions, pendingReturnPositions, depth2Statements.get(key));
			sat = m_SmtManager.getScript().checkSat();
			// Report benchmarks
			m_Tcbg.reportnewCheckSat();
			m_Tcbg.reportnewAssertedCodeBlocks(depth2Statements.get(key).size());
			if (sat == LBool.UNSAT) {
				return sat;
			}
		}
		return sat;
	}

	private LBool annotateAndAssertStmtsAccording3Heuristic(
			NestedWord<CodeBlock> trace, Collection<Integer> callPositions,
			Collection<Integer> pendingReturnPositions,
			Map<Integer, Set<Integer>> depth2Statements) {
		List<Integer> keysInDescendingOrder = new ArrayList<Integer>(depth2Statements.keySet()); 
		Collections.sort(keysInDescendingOrder, new Comparator<Integer>() {
			@Override
			public int compare(Integer i1, Integer i2) {
				return i2.compareTo(i1);
			}
		});
		LBool sat = null;
		for (Integer key : keysInDescendingOrder) {
			buildAnnotatedSsaAndAssertTermsWithPriorizedOrder(trace, callPositions, pendingReturnPositions, depth2Statements.get(key));
			sat = m_SmtManager.getScript().checkSat();
			// Report benchmarks
			m_Tcbg.reportnewCheckSat();
			m_Tcbg.reportnewAssertedCodeBlocks(depth2Statements.get(key).size());
			if (sat == LBool.UNSAT) {
				return sat;
			}
		}
		return sat;
	}
	private LBool annotateAndAssertStmtsAccording4Heuristic(
			NestedWord<CodeBlock> trace, Collection<Integer> callPositions,
			Collection<Integer> pendingReturnPositions,
			Map<Integer, Set<Integer>> depth2Statements) {
		LinkedList<Integer> depthAsQueue = new LinkedList<Integer>(depth2Statements.keySet()); 
		Collections.sort(depthAsQueue);
		LBool sat = null;
		boolean removeFirst = true;
		while (!depthAsQueue.isEmpty()) {
			int currentDepth = 0;
			if (removeFirst) {
				currentDepth = depthAsQueue.removeFirst();
			} else {
				currentDepth = depthAsQueue.removeLast();
			}
			removeFirst = !removeFirst;
			buildAnnotatedSsaAndAssertTermsWithPriorizedOrder(trace, callPositions, pendingReturnPositions, depth2Statements.get(currentDepth));
			sat = m_SmtManager.getScript().checkSat();
			// Report benchmarks
			m_Tcbg.reportnewCheckSat();
			m_Tcbg.reportnewAssertedCodeBlocks(depth2Statements.get(currentDepth).size());
			if (sat == LBool.UNSAT) {
				return sat;
			}
		}
		return sat;
	}

	private RelationWithTreeSet<ProgramPoint, Integer> computeRelationWithTreeSetForTrace(
			int lowerIndex, int upperIndex,
			List<ProgramPoint> pps) {
		RelationWithTreeSet<ProgramPoint, Integer> rwt = new RelationWithTreeSet<ProgramPoint, Integer>();
		for (int i = lowerIndex; i <= upperIndex; i++) {
			rwt.addPair(pps.get(i), i);
		}
		return rwt;
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
