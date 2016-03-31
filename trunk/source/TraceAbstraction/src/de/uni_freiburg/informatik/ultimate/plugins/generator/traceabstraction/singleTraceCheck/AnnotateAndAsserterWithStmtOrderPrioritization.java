/*
 * Copyright (C) 2014-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.math.BigDecimal;
import java.math.BigInteger;
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

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IAction;
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
 * General idea:
 * First, assert all statements which don't occur inside of a loop. Then, check for satisfiability. 
 * If the result of the satisfiability check is not unsatisfiable, then assert the rest of the statements, and return the 
 * result of the unsatisfiability check.
 
 ********* 2. Heuristic *********
 * General idea:
 * Assert statements in incremental order by their depth, and check after each step for satisfiability. E.g. first assert all
 * statements with depth 0, then assert all statements at depth 1, and so on.
 * 
 ********* 3. Heuristic *********
 * General idea:
 * Assert statements in decremental order by their depth, and check after each step for satisfiability. E.g. first assert all
 * statements with depth max_depth, then assert all statements of depth max_depth - 1, and so on.
 * 
 ********* 4. Heuristic *********
 * The 4.th heuristic is a mix-up of the 2nd the 3rd heuristic.
 *    
 ******** 5. Heuristic ************
 * General idea:
 * Assert statements that with small constants first. Then, check for satisfiability.
 * If the result of the satisfiability check is not unsatisfiable, then assert the rest of the statements, and return the 
 * result of the unsatisfiability check.
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
			IUltimateServiceProvider services) {
		super(smtManager, nestedSSA, aaacb, tcbg, services);
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
	
	/**
	 * Partition the statement positions between lowerIndex and upperIndex according to their depth. (See documentation for the meaning of 'depth').
	 * The result is stored in the map 'depth2Statements'.
	 * The partitioning is done recursively. 
	 */
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
	 * Add the position 'stmtPos' to the map 'depth2Statements' where the key is the given 'depth'.
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

	
	/**
	 * 
	 * Partition the statements of the given trace according to their depth.
	 */
	private Map<Integer, Set<Integer>> partitionStatementsAccordingDepth(NestedWord<? extends IAction> trace, RelationWithTreeSet<ProgramPoint, Integer> rwt,
			List<ProgramPoint> pps) {
		Map<Integer, Set<Integer>> depth2Statements = new HashMap<Integer, Set<Integer>>();
		
		dfsPartitionStatementsAccordingToDepth(0, trace.length(), 0, rwt, depth2Statements, pps);
		
		return depth2Statements;
	}
	
	@Override
	public void buildAnnotatedSsaAndAssertTerms() {
		List<ProgramPoint> pps = TraceCheckerUtils.getSequenceOfProgramPoints((NestedWord<CodeBlock>) m_Trace);
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
		} // Apply 5. Heuristic
		else if (m_AssertCodeBlocksOrder == AssertCodeBlockOrder.TERMS_WITH_SMALL_CONSTANTS_FIRST) {
			m_Satisfiable = annotateAndAssertStmtsAccording5Heuristic(m_Trace, callPositions,
					pendingReturnPositions);
		}
		else {
			throw new AssertionError("unknown heuristic " + m_AssertCodeBlocksOrder);
		}
		m_Logger.info("Conjunction of SSA is " + m_Satisfiable);
	}

	/**
	 * See class description!
	 */
	private LBool annotateAndAssertStmtsAccording2Heuristic(NestedWord<? extends IAction> trace,
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

	/**
	 * See class description!
	 */
	private LBool annotateAndAssertStmtsAccording3Heuristic(
			NestedWord<? extends IAction> trace, Collection<Integer> callPositions,
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
	
	/**
	 * See class description!
	 */
	private LBool annotateAndAssertStmtsAccording4Heuristic(
			NestedWord<? extends IAction> trace, Collection<Integer> callPositions,
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
	
	/**
	 * Determines whether the given term 't' contains a constant (a (real/natural) number) that is greater than the given
	 * size 'constantSize'.
	 */
	private boolean termHasConstantGreaterThan(Term t, int constantSize) {
		if (t instanceof ApplicationTerm) {
			Term[] args = ((ApplicationTerm)t).getParameters();
			for (int i = 0; i < args.length; i++) {
				if (termHasConstantGreaterThan(args[i], constantSize)) {
					return true;
				}
			}
		} else if (t instanceof ConstantTerm) {
			Object val = ((ConstantTerm)t).getValue();
			if (val instanceof BigInteger) {
				return (((BigInteger) val).compareTo(BigInteger.valueOf(constantSize)) > 0);
			} else if (val instanceof BigDecimal) {
				return (((BigDecimal) val).compareTo(BigDecimal.valueOf(constantSize)) > 0);
			}  else if (val instanceof Rational) {
				return (((Rational) val).compareTo(Rational.valueOf(constantSize, 1)) > 0);
			} else {
				throw new UnsupportedOperationException("ConstantTerm is neither BigInter nor BigDecimal, therefore comparison is not possible!");
			}
			
		} 
		return false;
	}

	
	/**
	 * Partition the statements of the given trace into two sets. The first set consists of the statements, which contain only constants 
	 * smaller than or equal to 'constantSize'. The second set contains the statements, which contain only constants greater than 'constantSize'. 
	 */
	private Set<Integer> partitionStmtsAccordingToConstantSize(NestedWord<? extends IAction> trace,	int constantSize) {
		Set<Integer> result = new HashSet<Integer>();
		
		for (int i = 0; i < trace.length(); i++) {
			Term t = ((CodeBlock) trace.getSymbolAt(i)).getTransitionFormula().getFormula();
			if (!termHasConstantGreaterThan(t, constantSize)) {
				result.add(i);
			}
		}
		return result;
	}
	
	/**
	 * See class description!
	 */
	private LBool annotateAndAssertStmtsAccording5Heuristic(
			NestedWord<? extends IAction> trace, Collection<Integer> callPositions,
			Collection<Integer> pendingReturnPositions) {
		// Choose statements that contains only constants <= constantSize and assert them
		int constantSize = 10;
		Set<Integer> stmtsToAssert = partitionStmtsAccordingToConstantSize(trace, constantSize);
		buildAnnotatedSsaAndAssertTermsWithPriorizedOrder(trace, callPositions, pendingReturnPositions, stmtsToAssert);
		LBool sat = m_SmtManager.getScript().checkSat();
		// Report benchmarks
		m_Tcbg.reportnewCheckSat();
		m_Tcbg.reportnewAssertedCodeBlocks(stmtsToAssert.size());
		if (sat == LBool.UNSAT) {
			return sat;
		}
		// Then assert the rest of statements
		Set<Integer> remainingStmts = integerSetDifference(getSetOfIntegerForGivenInterval(0, trace.length()), stmtsToAssert);
		buildAnnotatedSsaAndAssertTermsWithPriorizedOrder(trace, callPositions, pendingReturnPositions, 
				remainingStmts);
		sat = m_SmtManager.getScript().checkSat();
		// Report benchmarks
		m_Tcbg.reportnewCheckSat();
		m_Tcbg.reportnewAssertedCodeBlocks(remainingStmts.size());
		return sat;
	}

	/**
	 * TODO(Betim): DOcumentation!
	 */
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
	private void buildAnnotatedSsaAndAssertTermsWithPriorizedOrder(NestedWord<? extends IAction> trace, 
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
