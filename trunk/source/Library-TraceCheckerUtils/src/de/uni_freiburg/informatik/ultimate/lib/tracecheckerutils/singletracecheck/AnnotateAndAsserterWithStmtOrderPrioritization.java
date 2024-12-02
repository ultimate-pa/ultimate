/*
 * Copyright (C) 2014-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrderType;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.SmtFeatureHeuristicPartitioningType;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SMTFeatureExtractionTermClassifier;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashTreeRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * This class implements the possibility to partially (and in different order) annotate and assert the statements of a
 * trace in order to get better interpolants.
 *
 * Following heuristics are currently implemented: <br/>
 * <br/>
 * ********* 1. Heuristic ********* <br/>
 * General idea: First, assert all statements which don't occur inside of a loop. Then, check for satisfiability. If the
 * result of the satisfiability check is not unsatisfiable, then assert the rest of the statements, and return the
 * result of the unsatisfiability check. <br/>
 * <br/>
 ********* 2. Heuristic ********* <br/>
 * General idea: Assert statements in incremental order by their depth, and check after each step for satisfiability.
 * E.g. first assert all statements with depth 0, then assert all statements at depth 1, and so on. <br/>
 * <br/>
 ********* 3. Heuristic ********* <br/>
 * General idea: Assert statements in decremental order by their depth, and check after each step for satisfiability.
 * E.g. first assert all statements with depth max_depth, then assert all statements of depth max_depth - 1, and so
 * on.<br/>
 * <br/>
 ********* 4. Heuristic ********* <br/>
 * The 4.th heuristic is a mix-up of the 2nd the 3rd heuristic. <br/>
 * <br/>
 ******** 5. Heuristic ************ <br/>
 * General idea: Assert statements that with small constants first. Then, check for satisfiability. If the result of the
 * satisfiability check is not unsatisfiable, then assert the rest of the statements, and return the result of the
 * unsatisfiability check.
 *
 * @author musab@informatik.uni-freiburg.de
 */

public class AnnotateAndAsserterWithStmtOrderPrioritization<L extends IAction> extends AnnotateAndAsserter<L> {

	private final AssertCodeBlockOrder mAssertCodeBlocksOrder;
	private int mCheckSat;
	private final List<Object> mControlConfigurationSequence;

	public AnnotateAndAsserterWithStmtOrderPrioritization(final ManagedScript mgdScriptTc,
			final NestedFormulas<L, Term, Term> nestedSSA, final AnnotateAndAssertCodeBlocks<L> aaacb,
			final TraceCheckStatisticsGenerator tcbg, final AssertCodeBlockOrder assertCodeBlocksOrder,
			final IUltimateServiceProvider services) {
		super(mgdScriptTc, nestedSSA, aaacb, tcbg, services);
		mAssertCodeBlocksOrder = assertCodeBlocksOrder;
		mCheckSat = 0;
		mControlConfigurationSequence = nestedSSA.getControlConfigurations();
	}

	/**
	 * Returns a set of indices that represents all statements that is present in {@code trace}, but not in
	 * {@code statementIndices}.
	 */
	private static Set<Integer> getTraceDifference(final NestedWord<?> trace, final Set<Integer> statementIndices) {
		return IntStream.range(0, trace.length()).boxed().filter(x -> !statementIndices.contains(x))
				.collect(Collectors.toSet());
	}

	/**
	 * Partition the statement positions between lowerIndex and upperIndex according to their depth. (See documentation
	 * for the meaning of 'depth'). The result is stored in the map 'depth2Statements'. The partitioning is done
	 * recursively.
	 */
	private <LOC> void dfsPartitionStatementsAccordingToDepth(final Integer lowerIndex, final Integer upperIndex,
			final int depth, final HashTreeRelation<LOC, Integer> rwt,
			final Map<Integer, Set<Integer>> depth2Statements, final List<LOC> pps) {
		int i = lowerIndex;
		while (i < upperIndex) {
			// Is the current statement a loop entry?
			if (rwt.getImage(pps.get(i)).size() >= 2 && rwt.getImage(pps.get(i)).higher(i) != null
					&& rwt.getImage(pps.get(i)).higher(i) < upperIndex) {
				// the new upper index is the last occurrence of the same location
				final int newUpperIndex = rwt.getImage(pps.get(i)).lower(upperIndex);
				addStmtPositionToDepth(depth + 1, depth2Statements, i);
				// we consider the subtrace from i+1 to newUpperIndex as a loop
				// and apply the partitioning recursively on the subtrace
				dfsPartitionStatementsAccordingToDepth(i + 1, newUpperIndex, depth + 1, rwt, depth2Statements, pps);
				// continue at the position after the loop
				i = newUpperIndex;
			} else {
				addStmtPositionToDepth(depth, depth2Statements, i);
				i++;
			}
		}
	}

	/**
	 * Add the position 'stmtPos' to the map 'depth2Statements' where the key is the given 'depth'.
	 */
	private static void addStmtPositionToDepth(final int depth, final Map<Integer, Set<Integer>> depth2Statements,
			final int stmtPos) {
		if (depth2Statements.containsKey(depth)) {
			depth2Statements.get(depth).add(stmtPos);
		} else {
			final Set<Integer> s = new HashSet<>();
			s.add(stmtPos);
			depth2Statements.put(depth, s);
		}
	}

	/**
	 *
	 * Partition the statements of the given trace according to their depth.
	 */
	private <LOC> Map<Integer, Set<Integer>> partitionStatementsAccordingDepth(
			final NestedWord<? extends IAction> trace, final HashTreeRelation<LOC, Integer> rwt, final List<LOC> pps) {
		final Map<Integer, Set<Integer>> depth2Statements = new HashMap<>();

		dfsPartitionStatementsAccordingToDepth(0, trace.length(), 0, rwt, depth2Statements, pps);

		return depth2Statements;
	}

	@Override
	public void buildAnnotatedSsaAndAssertTerms() {
		assert mCheckSat == 0 : "You should not call this method twice";

		mAnnotSSA = new ModifiableNestedFormulas<>(mSSA.getCounterexample(), new TreeMap<Integer, Term>());

		mAnnotSSA.setPrecondition(mAnnotateAndAssertCodeBlocks.annotateAndAssertPrecondition());
		mAnnotSSA.setPostcondition(mAnnotateAndAssertCodeBlocks.annotateAndAssertPostcondition());
		final Collection<Integer> callPositions = new ArrayList<>();

		// Report benchmark
		mTcbg.reportNewCodeBlocks(mTrace.length());

		final AssertCodeBlockOrderType orderType = mAssertCodeBlocksOrder.getAssertCodeBlockOrderType();

		if (orderType == AssertCodeBlockOrderType.OUTSIDE_LOOP_FIRST1) {
			mSatisfiable = annotateAndAssert(mTrace, callPositions,
					partitionOutsideLoopFirst1(mTrace, mControlConfigurationSequence));
		} else if (orderType == AssertCodeBlockOrderType.OUTSIDE_LOOP_FIRST2) {
			mSatisfiable = annotateAndAssert(mTrace, callPositions,
					partitionOutsideLoopFirst2(mTrace, mControlConfigurationSequence));
		} else if (orderType == AssertCodeBlockOrderType.INSIDE_LOOP_FIRST1) {
			mSatisfiable = annotateAndAssert(mTrace, callPositions,
					partitionInsideLoopFirst1(mTrace, mControlConfigurationSequence));
		} else if (orderType == AssertCodeBlockOrderType.MIX_INSIDE_OUTSIDE) {
			mSatisfiable = annotateAndAssert(mTrace, callPositions,
					partitionMixInsideOutside(mTrace, mControlConfigurationSequence));
		} else if (orderType == AssertCodeBlockOrderType.TERMS_WITH_SMALL_CONSTANTS_FIRST) {
			mSatisfiable = annotateAndAssert(mTrace, callPositions, partitionSmallConstantsFirst(mTrace));
		} else if (orderType == AssertCodeBlockOrderType.SMT_FEATURE_HEURISTIC) {
			mSatisfiable = annotateAndAssert(mTrace, callPositions, partitionSmtFeatureHeuristic(mTrace));
		} else {
			throw new AssertionError("unknown heuristic " + mAssertCodeBlocksOrder);
		}
		mLogger.info("Assert order " + mAssertCodeBlocksOrder + " issued " + mCheckSat + " check-sat command(s)");
		mLogger.info("Conjunction of SSA is " + mSatisfiable);
	}

	private LBool annotateAndAssert(final NestedWord<? extends IAction> trace, final Collection<Integer> callPositions,
			final List<Set<Integer>> partitions) {
		LBool sat = null;
		boolean isFirstIteration = true;
		for (final Set<Integer> partition : partitions) {
			buildAnnotatedSsaAndAssertTermsWithPriorizedOrder(trace, callPositions, partition, isFirstIteration);
			mCheckSat++;
			sat = mMgdScriptTc.getScript().checkSat();
			// Report benchmarks
			mTcbg.reportNewCheckSat();
			mTcbg.reportNewAssertedCodeBlocks(partition.size());
			if (sat == LBool.UNSAT) {
				return sat;
			}
			isFirstIteration = false;
		}
		return sat;
	}

	private List<Set<Integer>> partitionOutsideLoopFirst1(final NestedWord<L> trace,
			final List<Object> controlConfigurationSequence) {
		final HashTreeRelation<Object, Integer> rwt =
				computeRelationWithTreeSetForTrace(0, trace.length(), controlConfigurationSequence);
		final Map<Integer, Set<Integer>> depth2Statements =
				partitionStatementsAccordingDepth(trace, rwt, controlConfigurationSequence);
		// Statements outside of a loop have depth 0.
		// First, annotate and assert the statements, which doesn't occur within a loop
		final Set<Integer> stmtsOutsideOfLoop = depth2Statements.get(0);
		if (stmtsOutsideOfLoop.size() == trace.length()) {
			return List.of(stmtsOutsideOfLoop);
		}
		final Set<Integer> stmtsWithinLoop = getTraceDifference(trace, stmtsOutsideOfLoop);
		return List.of(stmtsOutsideOfLoop, stmtsWithinLoop);
	}

	private List<Set<Integer>> partitionOutsideLoopFirst2(final NestedWord<L> trace,
			final List<Object> controlConfigurationSequence) {
		final HashTreeRelation<Object, Integer> rwt =
				computeRelationWithTreeSetForTrace(0, trace.length(), controlConfigurationSequence);
		final Map<Integer, Set<Integer>> depth2Statements =
				partitionStatementsAccordingDepth(trace, rwt, controlConfigurationSequence);
		return depth2Statements.keySet().stream().sorted().map(depth2Statements::get).toList();
	}

	/**
	 * See class description!
	 */
	private List<Set<Integer>> partitionInsideLoopFirst1(final NestedWord<L> trace,
			final List<Object> controlConfigurationSequence) {
		final HashTreeRelation<Object, Integer> rwt =
				computeRelationWithTreeSetForTrace(0, trace.length(), controlConfigurationSequence);
		final Map<Integer, Set<Integer>> depth2Statements =
				partitionStatementsAccordingDepth(trace, rwt, controlConfigurationSequence);
		return depth2Statements.keySet().stream().sorted((i1, i2) -> i2.compareTo(i1)).map(depth2Statements::get)
				.toList();
	}

	/**
	 * See class description!
	 */
	private List<Set<Integer>> partitionMixInsideOutside(final NestedWord<? extends IAction> trace,
			final List<Object> controlConfigurationSequence) {
		final HashTreeRelation<Object, Integer> rwt =
				computeRelationWithTreeSetForTrace(0, trace.length(), controlConfigurationSequence);
		final Map<Integer, Set<Integer>> depth2Statements =
				partitionStatementsAccordingDepth(trace, rwt, controlConfigurationSequence);
		final LinkedList<Integer> depthAsQueue = new LinkedList<>(depth2Statements.keySet());
		Collections.sort(depthAsQueue);
		final List<Set<Integer>> result = new ArrayList<>(depth2Statements.size());
		boolean removeFirst = true;
		while (!depthAsQueue.isEmpty()) {
			int currentDepth = 0;
			if (removeFirst) {
				currentDepth = depthAsQueue.removeFirst();
			} else {
				currentDepth = depthAsQueue.removeLast();
			}
			removeFirst = !removeFirst;
			result.add(depth2Statements.get(currentDepth));
		}
		return result;
	}

	/**
	 * Determines whether the given term 't' contains a constant (a (real/natural) number) that is greater than the
	 * given size 'constantSize'.
	 */
	private static boolean termHasConstantGreaterThan(final Term t, final int constantSize) {
		if (t instanceof ApplicationTerm) {
			final Term[] args = ((ApplicationTerm) t).getParameters();
			for (final Term arg : args) {
				if (termHasConstantGreaterThan(arg, constantSize)) {
					return true;
				}
			}
		} else if (t instanceof ConstantTerm) {
			final Object val = ((ConstantTerm) t).getValue();
			if (val instanceof BigInteger) {
				return ((BigInteger) val).compareTo(BigInteger.valueOf(constantSize)) > 0;
			} else if (val instanceof BigDecimal) {
				return ((BigDecimal) val).compareTo(BigDecimal.valueOf(constantSize)) > 0;
			} else if (val instanceof Rational) {
				return ((Rational) val).compareTo(Rational.valueOf(constantSize, 1)) > 0;
			} else {
				throw new UnsupportedOperationException(
						"ConstantTerm is neither BigInter nor BigDecimal, therefore comparison is not possible!");
			}

		}
		return false;
	}

	/**
	 * Partition the statements of the given trace into two sets. The first set consists of the statements, which
	 * contain only constants smaller than or equal to 'constantSize'. The second set contains the statements, which
	 * contain only constants greater than 'constantSize'.
	 */
	private static Set<Integer> partitionStmtsAccordingToConstantSize(final NestedWord<? extends IAction> trace,
			final int constantSize) {
		final Set<Integer> result = new HashSet<>();

		for (int i = 0; i < trace.length(); i++) {
			final Term t = trace.getSymbol(i).getTransformula().getFormula();
			if (!termHasConstantGreaterThan(t, constantSize)) {
				result.add(i);
			}
		}
		return result;
	}

	/**
	 * See class description!
	 */
	private List<Set<Integer>> partitionSmallConstantsFirst(final NestedWord<? extends IAction> trace) {
		// Choose statements that contains only constants <= constantSize and assert them
		final int constantSize = 10;
		final Set<Integer> stmtsWithSmallConstant = partitionStmtsAccordingToConstantSize(trace, constantSize);
		// Then assert the rest of statements
		return List.of(stmtsWithSmallConstant, getTraceDifference(trace, stmtsWithSmallConstant));
	}

	// Function to score a trace, using the SMTFeatureExtractionTermClassifier.
	private List<Triple<Term, Double, Integer>> scoreTrace(final NestedWord<? extends IAction> trace) {
		final List<Triple<Term, Double, Integer>> termScoreIndexTriples = new ArrayList<>();
		for (int i = 0; i < trace.length(); i++) {
			final SMTFeatureExtractionTermClassifier tc = new SMTFeatureExtractionTermClassifier();
			final Term term = trace.getSymbol(i).getTransformula().getFormula();
			tc.checkTerm(term);
			final Double score = tc.getScore(mAssertCodeBlocksOrder.getSmtFeatureHeuristicScoringMethod());
			termScoreIndexTriples.add(new Triple<>(term, score, i));
		}
		// sort reverse
		Collections.sort(termScoreIndexTriples, Comparator.comparing(p -> -p.getSecond()));
		return termScoreIndexTriples;
	}

	private static LinkedHashSet<Integer> getIndices(final List<Triple<Term, Double, Integer>> termScoreIndexTriples,
			final boolean random) {
		final List<Integer> indices = termScoreIndexTriples.stream().map(Triple<Term, Double, Integer>::getThird)
				.collect(Collectors.toList());
		if (random) {
			Collections.shuffle(indices);
		}
		return new LinkedHashSet<>(indices);
	}

	private void partitionFixedNumberOfPartitions(final LinkedHashSet<LinkedHashSet<Integer>> partitions,
			final List<Triple<Term, Double, Integer>> termScoreIndexTriples, final boolean random) {

		// The incremental Strategy creates N partitions.
		// Example:
		// Indices = [1,2,3,4,5,6]
		// N = 4
		// percentage_per_chunk = 1 / 4 = 0.25
		// Chunk_size = 2
		// Partitions = [1,2], [3,4], [5,6]

		final LinkedHashSet<Integer> indices = getIndices(termScoreIndexTriples, random);

		final int chunksize = (int) Math.ceil(
				termScoreIndexTriples.size() * (1.0 / mAssertCodeBlocksOrder.getSmtFeatureHeuristicNumPartitions()));

		LinkedHashSet<Integer> currentChunk = new LinkedHashSet<>();

		int numProcessed = 0;

		for (final int index : indices) {
			currentChunk.add(index);
			numProcessed += 1;
			if (currentChunk.size() == chunksize || numProcessed == indices.size()) {
				partitions.add(new LinkedHashSet<>(currentChunk));
				currentChunk = new LinkedHashSet<>();
			}
		}
	}

	private void partitionUsingThreshold(final LinkedHashSet<LinkedHashSet<Integer>> partitions,
			final List<Triple<Term, Double, Integer>> termScoreIndexTriples) {

		// The incremental Strategy creates N partitions.
		// Example:
		// Indices = [1,2,3,4,5,6]
		// N = 4
		// percentage_per_chunk = 1 / 4 = 0.25
		// Chunk_size = 2
		// Partitions = [1,2], [3,4], [5,6]

		final LinkedHashSet<Integer> partitionOne = new LinkedHashSet<>();
		final LinkedHashSet<Integer> partitionTwo = new LinkedHashSet<>();

		for (final Triple<Term, Double, Integer> triple : termScoreIndexTriples) {
			final Double score = triple.getSecond();
			final Integer index = triple.getThird();
			if (score >= mAssertCodeBlocksOrder.getSmtFeatureHeuristicThreshold()) {
				partitionOne.add(index);
			} else {
				partitionTwo.add(index);
			}
		}

		if (!partitionOne.isEmpty()) {
			partitions.add(partitionOne);
		}
		if (!partitionTwo.isEmpty()) {
			partitions.add(partitionTwo);
		}
	}

	// Function to partition a list of Terms according to their scores.
	private List<Set<Integer>>
			partitionStmtsAccordingToTermScores(final List<Triple<Term, Double, Integer>> termScoreIndexTriples) {
		final LinkedHashSet<LinkedHashSet<Integer>> partitions = new LinkedHashSet<>();
		final SmtFeatureHeuristicPartitioningType partitioningType =
				mAssertCodeBlocksOrder.getSmtFeatureHeuristicPartitioningType();
		switch (partitioningType) {
		case FIXED_NUM_PARTITIONS:
			partitionFixedNumberOfPartitions(partitions, termScoreIndexTriples, false);
			break;
		case THRESHOLD:
			partitionUsingThreshold(partitions, termScoreIndexTriples);
			break;
		default:
			throw new UnsupportedOperationException("Unknown partitioning type " + partitioningType);
		}
		assert !partitions.isEmpty();
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("TermScoreTriples: " + termScoreIndexTriples.toString());
			mLogger.debug("Partitions: " + partitions.toString());
		}
		return new ArrayList<>(partitions);
	}

	private List<Set<Integer>> partitionSmtFeatureHeuristic(final NestedWord<? extends IAction> trace) {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Trace: " + trace.toString());
		}
		// Score Trace Terms and order them according to score.
		return partitionStmtsAccordingToTermScores(scoreTrace(trace));
	}

	/**
	 * TODO(Betim): DOcumentation!
	 */
	private static <LOC> HashTreeRelation<LOC, Integer> computeRelationWithTreeSetForTrace(final int lowerIndex,
			final int upperIndex, final List<LOC> pps) {
		final HashTreeRelation<LOC, Integer> rwt = new HashTreeRelation<>();
		for (int i = lowerIndex; i <= upperIndex; i++) {
			rwt.addPair(pps.get(i), i);
		}
		return rwt;
	}

	/**
	 * Annotate and assert every statement <i>i</i> from the given trace, such that <i>i</i> is an element of the given
	 * integer set stmtsToAssert.
	 */
	private void buildAnnotatedSsaAndAssertTermsWithPriorizedOrder(final NestedWord<? extends IAction> trace,
			final Collection<Integer> callPositions, final Set<Integer> stmtsToAssert,
			final boolean assertPendingContexts) {
		for (final Integer i : stmtsToAssert) {
			if (trace.isCallPosition(i)) {
				callPositions.add(i);
				mAnnotSSA.setGlobalVarAssignmentAtPos(i,
						mAnnotateAndAssertCodeBlocks.annotateAndAssertGlobalVarAssignemntCall(i));
				mAnnotSSA.setLocalVarAssignmentAtPos(i,
						mAnnotateAndAssertCodeBlocks.annotateAndAssertLocalVarAssignemntCall(i));
				mAnnotSSA.setOldVarAssignmentAtPos(i,
						mAnnotateAndAssertCodeBlocks.annotateAndAssertOldVarAssignemntCall(i));
			} else {
				mAnnotSSA.setFormulaAtNonCallPos(i, mAnnotateAndAssertCodeBlocks.annotateAndAssertNonCall(i));
			}
		}

		if (assertPendingContexts) {
			// Number that the pending context. The first pending context has
			// number -2, the second -3, the third -4, ...
			// (the number -1 is reserved for the precondition)
			int pendingContextCode = -1 - mSSA.getTrace().getPendingReturns().size();
			for (final Integer positionOfPendingReturn : mSSA.getTrace().getPendingReturns().keySet()) {
				assert trace.isPendingReturn(positionOfPendingReturn);
				{
					final Term annotated = mAnnotateAndAssertCodeBlocks
							.annotateAndAssertPendingContext(positionOfPendingReturn, pendingContextCode);
					mAnnotSSA.setPendingContext(positionOfPendingReturn, annotated);
				}
				{
					final Term annotated =
							mAnnotateAndAssertCodeBlocks.annotateAndAssertLocalVarAssignemntPendingContext(
									positionOfPendingReturn, pendingContextCode);
					mAnnotSSA.setLocalVarAssignmentAtPos(positionOfPendingReturn, annotated);
				}
				{
					final Term annotated = mAnnotateAndAssertCodeBlocks.annotateAndAssertOldVarAssignemntPendingContext(
							positionOfPendingReturn, pendingContextCode);
					mAnnotSSA.setOldVarAssignmentAtPos(positionOfPendingReturn, annotated);
				}
				pendingContextCode++;
			}
		}
	}

}
