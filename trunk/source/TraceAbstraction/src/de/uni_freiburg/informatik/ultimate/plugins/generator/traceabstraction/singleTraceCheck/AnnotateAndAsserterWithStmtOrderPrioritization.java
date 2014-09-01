package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
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
 * This class implements the possibility to partially annotate and assert the statements of a trace in order
 * to get better interpolants.
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class AnnotateAndAsserterWithStmtOrderPrioritization extends AnnotateAndAsserter {
	
////	TODO: Document heuristics
//	/**
//	 * 1. Heuristic:
//	 */
//	private static boolean m_Heuristic_1 = !true;
//	
//	/**
//	 * 2. Heuristic: 
//	 */
//	private static boolean m_Heuristic_2 = !true;
//
//	/**
//	 * 3. Heuristic: ..
//	 */
//	private static boolean m_Heuristic_3 = true;
	
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
	 * Returns the positions of program-points, which are equal to each other. (E.g. Program point x occurs at positions
	 * 1, 3, 9, then a treeset containing those values is returned.) 
	 * It considers the trace only at the interval [lowerIndex, upperIndex].
	 */
	private TreeSet<Integer> getPositionsOfLoopStatements(NestedWord<CodeBlock> trace, int lowerIndex, int upperIndex,
			RelationWithTreeSet<ProgramPoint, Integer> rwt) {
//		assert lowerIndex >= 0 : "Lower index is negative";
//		assert upperIndex > lowerIndex : "Upper index is <= lower index";
//		assert upperIndex <= trace.length() : "Upper index is out of range";
//		
//		RelationWithTreeSet<ProgramPoint, Integer> rwt = new RelationWithTreeSet<ProgramPoint, Integer>();
//		for (int i = lowerIndex; i <= upperIndex; i++) {
//			rwt.addPair(pps.get(i), i);
//		}
		List<ProgramPoint> pps = TraceCheckerUtils.getSequenceOfProgramPoints(trace);
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

	

	private List<TreeSet<Integer>> getListOfLoopProgramPoints(
			Integer lowerIndex, Integer upperIndex,
			RelationWithTreeSet<ProgramPoint, Integer> rwt,
			NestedWord<CodeBlock> trace) {
		List<TreeSet<Integer>> listOfLoopProgramPoints = new LinkedList<TreeSet<Integer>>();
		TreeSet<Integer> loopProgramPoints = getPositionsOfLoopStatements(trace, lowerIndex, upperIndex, rwt);
		loopProgramPoints = getIntersectionSet_vs_Interval(loopProgramPoints, lowerIndex, upperIndex);
		
		if (loopProgramPoints.isEmpty()) return  listOfLoopProgramPoints;
		
		int leastIndex = loopProgramPoints.first();
		listOfLoopProgramPoints.add(loopProgramPoints);
		while (leastIndex < upperIndex) {
			TreeSet<Integer> loopProgramPointsTemp = getPositionsOfLoopStatements(trace, leastIndex, upperIndex, rwt);
			// Check, whether we have the same loop
			if (loopProgramPointsTemp.last() == loopProgramPoints.last()) {
				break;
			} else {
				loopProgramPoints = loopProgramPointsTemp;
				loopProgramPoints = (TreeSet<Integer>) getIntersectionSet_vs_Interval(loopProgramPoints, leastIndex, upperIndex);
				if (leastIndex == loopProgramPoints.first()) {
					leastIndex = loopProgramPoints.ceiling(leastIndex);
					if ((Integer)leastIndex == null) break;
				} else {
					leastIndex = loopProgramPointsTemp.first();
				}
				listOfLoopProgramPoints.add(loopProgramPoints);
			}
		}
		return listOfLoopProgramPoints;
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
		Map.Entry<Integer, Integer> indicesOfStmtThatOccursTwice = getIndicesOfProgramPointThatOccursTwice(m_Trace, 0, m_Trace.length());
		int lowerPositionOfPPThatOccursTwice = indicesOfStmtThatOccursTwice.getKey();
		int upperIndexOfStmtThatOccursTwice =  indicesOfStmtThatOccursTwice.getValue();
		
		Set<Integer> stmtsWithinLoop = getSetOfIntegerForGivenInterval(lowerPositionOfPPThatOccursTwice, upperIndexOfStmtThatOccursTwice);
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
		if (m_AssertCodeBlocksOrder == AssertCodeBlockOrder.OUTSIDE_LOOP_FIRST1) {
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
		else if (m_AssertCodeBlocksOrder == AssertCodeBlockOrder.OUTSIDE_LOOP_FIRST2) {
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
					indicesOfStmtThatOccursTwice = getIndicesOfProgramPointThatOccursTwice(m_Trace, lowerPositionOfPPThatOccursTwice + 1, 
							upperIndexOfStmtThatOccursTwice-1);
					lowerPositionOfPPThatOccursTwice = indicesOfStmtThatOccursTwice.getKey();
					upperIndexOfStmtThatOccursTwice =  indicesOfStmtThatOccursTwice.getValue();
					// update the set of statements which are already asserted
					Set<Integer> stmtsWithinLoopOld = stmtsWithinLoop; 
					stmtsWithinLoop = getSetOfIntegerForGivenInterval(lowerPositionOfPPThatOccursTwice, upperIndexOfStmtThatOccursTwice);
					stmtsOutsideOfLoop = integerSetDifference(stmtsWithinLoopOld, stmtsWithinLoop);
					stmtsAlreadyAsserted.addAll(stmtsOutsideOfLoop);
				}
			}
		} 
		// Apply 3. heuristic
		else if (m_AssertCodeBlocksOrder == AssertCodeBlockOrder.OUTSIDE_LOOP_FIRST3) {
			Map<Integer, Set<Integer>> depth2Statements = partitionStatementsAccordingDepth(m_Trace, rwt, pps);
			
			m_Satisfiable = annotateAndAssertStmtsAccording3Heuristic(m_Trace, callPositions,
					pendingReturnPositions, depth2Statements);
		}// Apply 4. heuristic
		else if (m_AssertCodeBlocksOrder == AssertCodeBlockOrder.INSIDE_LOOP_FIRST1) {
			Map<Integer, Set<Integer>> depth2Statements = partitionStatementsAccordingDepth(m_Trace, rwt, pps);
			
			m_Satisfiable = annotateAndAssertStmtsAccording4Heuristic(m_Trace, callPositions,
					pendingReturnPositions, depth2Statements);
		} else {
			throw new AssertionError("unknown value " + m_AssertCodeBlocksOrder);
		}
		mLogger.info("Conjunction of SSA is " + m_Satisfiable);
	}
	

	private LBool annotateAndAssertStmtsAccording4Heuristic(
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

	private RelationWithTreeSet<ProgramPoint, Integer> computeRelationWithTreeSetForTrace(
			int lowerIndex, int upperIndex,
			List<ProgramPoint> pps) {
		RelationWithTreeSet<ProgramPoint, Integer> rwt = new RelationWithTreeSet<ProgramPoint, Integer>();
		for (int i = lowerIndex; i <= upperIndex; i++) {
			rwt.addPair(pps.get(i), i);
		}
		return rwt;
	}

	private LBool annotateAndAssertStmtsAccording3Heuristic(NestedWord<CodeBlock> trace,
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
	
//	private LBool annotateAndAssertStmtsAccording3Heuristic(NestedWord<CodeBlock> trace,
//			Set<Integer> unassertedStmts, TreeSet<Integer> loopProgramPoints,
//			Collection<Integer> callPositions,
//			Collection<Integer> pendingReturnPositions,
//			RelationWithTreeSet<ProgramPoint, Integer> rwt,
//			List<ProgramPoint> pps
//			) {
//		Set<Integer> stmtsWithinLoop = null;
//		if (loopProgramPoints.isEmpty()) {
//			stmtsWithinLoop = new HashSet<Integer>();
//		} else {
//			stmtsWithinLoop = getSetOfIntegerForGivenInterval(loopProgramPoints.first(), loopProgramPoints.last());
//		}
//		Set<Integer> stmtsOutsideOfLoop = integerSetDifference(unassertedStmts, stmtsWithinLoop);
//		
//		// Annotate and assert the statements which don't occur inside or in-between the @param loopProgramPoints 
//		buildAnnotatedSsaAndAssertTermsWithPriorizedOrder(trace, callPositions, pendingReturnPositions, stmtsOutsideOfLoop);
//		LBool sat = m_SmtManager.getScript().checkSat();
//		// Report benchmarks
//		m_Tcbg.reportnewCheckSat();
//		m_Tcbg.reportnewAssertedCodeBlocks(stmtsOutsideOfLoop.size());
//		if (sat == LBool.UNSAT) {
//			return sat;
//		}
//		unassertedStmts = integerSetDifference(unassertedStmts, stmtsOutsideOfLoop);
//		List<Map.Entry<Integer, Integer>> parts = getPartitionsOfStatements(new ArrayList<Integer>(loopProgramPoints));
//		while (true) {
//			loopProgramPoints = new TreeSet<Integer>();
//			for (int i = 0; i < parts.size(); i++) {
//				Set<Integer> stmtsToAssert = new HashSet<Integer>();
//				Map.Entry<Integer, Integer> currentPart = parts.get(i);
//				loopProgramPoints.addAll(getPositionsOfLoopStatements(trace, currentPart.getKey() + 1, currentPart.getValue()-1, rwt));
//				
//				// If it is not the last part, then add both the start and the end value of the
//				// current part to stmtsToAssert
//				if (i < parts.size() - 1) {
//					stmtsToAssert.add(currentPart.getKey());
//					stmtsToAssert.add(currentPart.getValue());
//				} 
//				// Add statements from within the current part, if they are no loop statements
////				stmtsToAssert.addAll(getPositionsOfSingleStatementsFromPart(currentPart.getKey(), currentPart.getValue(), rwt));
//				Set<Integer> singleStmts = getPositionsOfSingleStatementsFromPart(currentPart.getKey()+1, currentPart.getValue()-1, 
//						rwt, pps);
//				if (singleStmts.isEmpty() && loopProgramPoints.isEmpty()) {
//					singleStmts.addAll(getSetOfIntegerForGivenInterval(currentPart.getKey(), currentPart.getValue()));
//				} else if (!loopProgramPoints.isEmpty()) {
//					stmtsToAssert.add(currentPart.getKey());
//					stmtsToAssert.add(loopProgramPoints.last());
//				} 
//				stmtsToAssert.addAll(singleStmts);
//				// Make sure, that no statements will be asserted more times
//				stmtsToAssert.retainAll(unassertedStmts);
//				if (!stmtsToAssert.isEmpty()) {
//					buildAnnotatedSsaAndAssertTermsWithPriorizedOrder(trace, callPositions, pendingReturnPositions, stmtsToAssert);
//					sat = m_SmtManager.getScript().checkSat();
//					// Report benchmarks
//					m_Tcbg.reportnewCheckSat();
//					m_Tcbg.reportnewAssertedCodeBlocks(stmtsToAssert.size());
//					if (sat == LBool.UNSAT) {
//						return sat;
//					}
//				}
//				// If all stmts have been asserted, then return
//				unassertedStmts = integerSetDifference(unassertedStmts, stmtsToAssert);
//			}
//			
//			if (unassertedStmts.isEmpty()) {
//				return sat;
//			}
//			// Otherwise:
//			parts = getPartitionsOfStatements(new ArrayList<Integer>(loopProgramPoints));
//		}
//	}
	
	private TreeSet<Integer> getIntersectionSet_vs_Interval(Set<Integer> s, int lowerIndex, int upperIndex) {
		TreeSet<Integer> result = new TreeSet<Integer>();
		for (Integer i : s) {
			if (i >= lowerIndex && i <= upperIndex) {
				result .add(i);
			}
		}
		return result;
	}
	
	private Set<Integer> getPositionsOfSingleStatementsFromPart(int lowerIndex, int upperIndex, 
			RelationWithTreeSet<ProgramPoint, Integer> rwt,
			List<ProgramPoint> pps) {
		Set<Integer> result = new HashSet<Integer>();
		if (lowerIndex > upperIndex) {
			return new HashSet<Integer>();
		} else if (lowerIndex == upperIndex) {
			result.add(lowerIndex);
			return result;
		}
		
		for (int i = lowerIndex; i <= upperIndex; i++) {
			if (rwt.getImage(pps.get(i)).size() >= 1) {
				Set<Integer> tempResult = getIntersectionSet_vs_Interval(rwt.getImage(pps.get(i)), lowerIndex, upperIndex);
				if (tempResult.size() == 1) {
					result.addAll(tempResult);
				}
				TreeSet<Integer> loopPositionsAsTreeSet = (TreeSet<Integer>) rwt.getImage(pps.get(i));
				if (loopPositionsAsTreeSet.first() == lowerIndex && loopPositionsAsTreeSet.last() == upperIndex) {
					break;
				}
				
			} 
		}
		return result;
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
