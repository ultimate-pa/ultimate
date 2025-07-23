/*
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2024 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2024 University of Freiburg
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

import java.util.List;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.TraceCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.assertorders.AssertOrderInsideLoopFirst1;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.assertorders.AssertOrderMixInsideOutside;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.assertorders.AssertOrderNotIncrementally;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.assertorders.AssertOrderOutsideLoopFirst1;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.assertorders.AssertOrderOutsideLoopFirst2;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.assertorders.AssertOrderShuffledSingletons;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.assertorders.AssertOrderSmallConstantsFirst;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.assertorders.AssertOrderSmtFeatureHeuristic;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.assertorders.IAssertOrder;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.assertorders.WitnessGuidedAssertOrder;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * This class implements the possibility to partially (and in different order) annotate and assert the statements of a
 * trace in order to get better interpolants.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Betimt Musa (musab@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */

public class AnnotateAndAsserter<L extends IAction> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	private final ManagedScript mMgdScriptTc;

	private LBool mSatisfiable;
	private final NestedFormulas<L, Term, Term> mSSA;
	private ModifiableNestedFormulas<L, Term, Term> mAnnotSSA;

	private final AnnotateAndAssertCodeBlocks<L> mAnnotateAndAssertCodeBlocks;

	private final TraceCheckStatisticsGenerator mTcbg;

	private final AssertCodeBlockOrder mAssertCodeBlocksOrder;
	private int mCheckSat;
	private int mAssertedStatements;

	public AnnotateAndAsserter(final ManagedScript mgdScriptTc, final NestedFormulas<L, Term, Term> nestedSSA,
			final AnnotateAndAssertCodeBlocks<L> aaacb, final TraceCheckStatisticsGenerator tcbg,
			final AssertCodeBlockOrder assertCodeBlocksOrder, final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(TraceCheckerUtils.PLUGIN_ID);
		mMgdScriptTc = mgdScriptTc;
		mSSA = nestedSSA;
		mAnnotateAndAssertCodeBlocks = aaacb;
		mTcbg = tcbg;
		mAssertCodeBlocksOrder = assertCodeBlocksOrder;
		mCheckSat = 0;
		mAssertedStatements = 0;
		buildAnnotatedSsaAndAssertTerms();
	}

	private void buildAnnotatedSsaAndAssertTerms() {
		mAnnotSSA = new ModifiableNestedFormulas<>(mSSA.getCounterexample(), new TreeMap<Integer, Term>());

		mAnnotSSA.setPrecondition(mAnnotateAndAssertCodeBlocks.annotateAndAssertPrecondition());
		mAnnotSSA.setPostcondition(mAnnotateAndAssertCodeBlocks.annotateAndAssertPostcondition());

		// Report benchmark
		mTcbg.reportNewCodeBlocks(mSSA.getCounterexample().length());

		// TODO: For testing, WitnessGuidedAssertOrder is hardcoded here.
		// What is the best way to handle this here? If we are not using witness guided verification, we just use the
		// underlying assert order from getAssertOrder here (as there are no WitnessAssumptions in this case).
		final List<Set<Integer>> partitions = new WitnessGuidedAssertOrder<>(getAssertOrder(mAssertCodeBlocksOrder))
				.partition(mSSA.getCounterexample());

		mLogger.info(String.format("Assert order %s partitioned %s statements into %s equivalence classes.",
				mAssertCodeBlocksOrder, mSSA.getCounterexample().length(), partitions.size()));
		mSatisfiable = annotateAndAssert(mSSA.getTrace(), partitions);
		mLogger.info(String.format("Assert order %s issued %s check-sat command(s) and asserted %s of %s statements.",
				mAssertCodeBlocksOrder, mCheckSat, mAssertedStatements, mSSA.getCounterexample().length()));

		mLogger.info("Assert order " + mAssertCodeBlocksOrder + " issued " + mCheckSat + " check-sat command(s)");
		mLogger.info("Conjunction of SSA is " + mSatisfiable);
	}

	private IAssertOrder<L> getAssertOrder(final AssertCodeBlockOrder order) {
		return switch (order.getAssertCodeBlockOrderType()) {
		case NOT_INCREMENTALLY -> new AssertOrderNotIncrementally<>();
		case OUTSIDE_LOOP_FIRST1 -> new AssertOrderOutsideLoopFirst1<>();
		case OUTSIDE_LOOP_FIRST2 -> new AssertOrderOutsideLoopFirst2<>();
		case INSIDE_LOOP_FIRST1 -> new AssertOrderInsideLoopFirst1<>();
		case MIX_INSIDE_OUTSIDE -> new AssertOrderMixInsideOutside<>();
		case TERMS_WITH_SMALL_CONSTANTS_FIRST -> new AssertOrderSmallConstantsFirst<>();
		case SMT_FEATURE_HEURISTIC -> new AssertOrderSmtFeatureHeuristic<>(order.getSmtFeatureHeuristicScoringMethod(),
				order.getSmtFeatureHeuristicNumPartitions(), order.getSmtFeatureHeuristicThreshold(),
				order.getSmtFeatureHeuristicPartitioningType(), mLogger);
		case SHUFFLED_SINGLETONS -> new AssertOrderShuffledSingletons<>();
		};
	}

	private LBool annotateAndAssert(final NestedWord<? extends IAction> trace, final List<Set<Integer>> partitions) {
		LBool sat = null;
		boolean isFirstIteration = true;
		for (final Set<Integer> partition : partitions) {
			buildAnnotatedSsaAndAssertTermsWithPriorizedOrder(trace, partition, isFirstIteration);
			mAssertedStatements += partition.size();
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
			final Set<Integer> stmtsToAssert, final boolean assertPendingContexts) {
		for (final Integer i : stmtsToAssert) {
			if (trace.isCallPosition(i)) {
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

	public LBool isInputSatisfiable() {
		return mSatisfiable;
	}

	public NestedFormulas<L, Term, Term> getAnnotatedSsa() {
		return mAnnotSSA;
	}

}
