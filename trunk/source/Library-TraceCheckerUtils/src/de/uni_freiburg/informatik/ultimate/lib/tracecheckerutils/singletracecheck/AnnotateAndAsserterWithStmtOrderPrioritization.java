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

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;

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

	@Override
	public void buildAnnotatedSsaAndAssertTerms() {
		assert mCheckSat == 0 : "You should not call this method twice";

		mAnnotSSA = new ModifiableNestedFormulas<>(mSSA.getCounterexample(), new TreeMap<Integer, Term>());

		mAnnotSSA.setPrecondition(mAnnotateAndAssertCodeBlocks.annotateAndAssertPrecondition());
		mAnnotSSA.setPostcondition(mAnnotateAndAssertCodeBlocks.annotateAndAssertPostcondition());
		final Collection<Integer> callPositions = new ArrayList<>();

		// Report benchmark
		mTcbg.reportNewCodeBlocks(mTrace.length());

		final List<Set<Integer>> partitions =
				getAssertOrder(mAssertCodeBlocksOrder).partitionTrace(mTrace, mControlConfigurationSequence);

		mSatisfiable = annotateAndAssert(mTrace, callPositions, partitions);
		mLogger.info("Assert order " + mAssertCodeBlocksOrder + " issued " + mCheckSat + " check-sat command(s)");
		mLogger.info("Conjunction of SSA is " + mSatisfiable);
	}

	private AssertOrder<L> getAssertOrder(final AssertCodeBlockOrder order) {
		switch (order.getAssertCodeBlockOrderType()) {
		case OUTSIDE_LOOP_FIRST1:
			return new AssertOrderOutsideLoopFirst1<>();
		case OUTSIDE_LOOP_FIRST2:
			return new AssertOrderOutsideLoopFirst2<>();
		case INSIDE_LOOP_FIRST1:
			return new AssertOrderInsideLoopFirst1<>();
		case MIX_INSIDE_OUTSIDE:
			return new AssertOrderMixInsideOutside<>();
		case TERMS_WITH_SMALL_CONSTANTS_FIRST:
			return new AssertOrderSmallConstantsFirst<>();
		case SMT_FEATURE_HEURISTIC:
			return new AssertOrderSmtFeatureHeuristic<>(order.getSmtFeatureHeuristicScoringMethod(),
					order.getSmtFeatureHeuristicNumPartitions(), order.getSmtFeatureHeuristicThreshold(),
					order.getSmtFeatureHeuristicPartitioningType(), mLogger);
		default:
			throw new AssertionError("unknown heuristic " + order);
		}
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
