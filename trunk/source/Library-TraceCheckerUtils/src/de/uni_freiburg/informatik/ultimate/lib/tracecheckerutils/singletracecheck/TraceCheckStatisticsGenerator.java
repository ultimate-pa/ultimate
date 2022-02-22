/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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

import java.lang.reflect.Field;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils.FormulaSize;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil.Reflected;
import de.uni_freiburg.informatik.ultimate.util.statistics.BaseStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.DefaultMeasureDefinitions;
import de.uni_freiburg.informatik.ultimate.util.statistics.MeasureDefinition;
import de.uni_freiburg.informatik.ultimate.util.statistics.measures.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.util.statistics.measures.TimeTracker;

public class TraceCheckStatisticsGenerator extends BaseStatisticsDataProvider {

	public enum InterpolantType {
		Craig, Forward, Backward
	}

	public static final String INTERPOLATION_COMPUTATION_TIME = "InterpolantComputationTime";
	public static final String SATISFIABILITY_ANALYSIS_TIME = "SatisfiabilityAnalysisTime";
	public static final String INTERPOLANT_COMPUTATIONS = "InterpolantComputations";
	public static final String PERFECT_INTERPOLANT_SEQUENCES = "PerfectInterpolantSequences";

	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mSsaConstructionTime = new TimeTracker();

	@Reflected(prettyName = SATISFIABILITY_ANALYSIS_TIME)
	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mSatisfiabilityAnalysisTime = new TimeTracker();

	@Reflected(prettyName = INTERPOLATION_COMPUTATION_TIME)
	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mInterpolantComputationTime = new TimeTracker();

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mNumberOfCodeBlocks;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mNumberOfCodeBlocksAsserted;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mNumberOfCheckSat;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mConstructedInterpolants;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mQuantifiedInterpolants;

	@Statistics(type = DefaultMeasureDefinitions.LONG_COUNTER)
	private long mSizeOfPredicates;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mNumberOfNonLiveVariables;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mConjunctsInSsa;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mConjunctsInUnsatCore;

	@Reflected(prettyName = INTERPOLANT_COMPUTATIONS)
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mInterpolantComputations;

	@Reflected(prettyName = PERFECT_INTERPOLANT_SEQUENCES)
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mPerfectInterpolantSequences;

	@Statistics(type = DefaultMeasureDefinitions.BACKWARD_COVERING_INFORMATION)
	private BackwardCoveringInformation mInterpolantCoveringCapability = new BackwardCoveringInformation(0, 0);

	private final boolean mCollectInterpolatSequenceStatistics;

	public TraceCheckStatisticsGenerator(final IToolchainStorage storage,
			final boolean collectInterpolatSequenceStatistics) {
		super(storage);
		mCollectInterpolatSequenceStatistics = collectInterpolatSequenceStatistics;
	}

	/**
	 * Tell the Benchmark that the checked trace has n CodeBlocks
	 */
	public void reportNewCodeBlocks(final int n) {
		mNumberOfCodeBlocks = mNumberOfCodeBlocks + n;
	}

	/**
	 * Tell the Benchmark that n CodeBlocks have been asserted additionally
	 */
	public void reportNewAssertedCodeBlocks(final int n) {
		mNumberOfCodeBlocksAsserted = mNumberOfCodeBlocksAsserted + n;
	}

	/**
	 * Tell the Benchmark we did another check sat
	 */
	public void reportNewCheckSat() {
		mNumberOfCheckSat++;
	}

	public void setConjunctsInSSA(final int conjunctsInSSA, final int conjunctsInUC) {
		assert mConjunctsInSsa == 0 : "have already been set";
		assert mConjunctsInUnsatCore == 0 : "have already been set";
		mConjunctsInSsa = conjunctsInSSA;
		mConjunctsInUnsatCore = conjunctsInUC;
	}

	public void reportSequenceOfInterpolants(final List<IPredicate> interpolants,
			final InterpolantType interpolantType) {
		if (!mCollectInterpolatSequenceStatistics) {
			return;
		}
		for (final IPredicate pred : interpolants) {
			mConstructedInterpolants++;

			final boolean isQuantified = !QuantifierUtils.isQuantifierFree(pred.getFormula());
			if (isQuantified) {
				mQuantifiedInterpolants++;
			}
		}
		mSizeOfPredicates +=
				computeLongSumOfIntArray(PredicateUtils.computeDagSizeOfPredicates(interpolants, FormulaSize.TREESIZE));
	}

	private static long computeLongSumOfIntArray(final long[] arr) {
		long sum = 0;
		for (int i = 0; i < arr.length; i++) {
			sum += arr[i];
		}
		return sum;
	}

	public void reportNumberOfNonLiveVariables(final int numberOfNonLiveVariables,
			final InterpolantType interpolantType) {
		mNumberOfNonLiveVariables += numberOfNonLiveVariables;
	}

	public void reportInterpolantComputation() {
		mInterpolantComputations++;
	}

	public void reportPerfectInterpolantSequences() {
		mPerfectInterpolantSequences++;
	}

	public void addBackwardCoveringInformation(final BackwardCoveringInformation bci) {
		mInterpolantCoveringCapability = new BackwardCoveringInformation(mInterpolantCoveringCapability, bci);
	}

	public boolean isCollectingInterpolantSequenceStatistics() {
		return mCollectInterpolatSequenceStatistics;
	}

	public void startSsaConstructionTime() {
		mSsaConstructionTime.start();
	}

	public void stopSsaConstructionTime() {
		mSsaConstructionTime.stop();
	}

	public void startSatisfiabilityAnalysisTime() {
		mSatisfiabilityAnalysisTime.start();
	}

	public void stopSatisfiabilityAnalysisTime() {
		mSatisfiabilityAnalysisTime.stop();
	}

	public void startInterpolantComputationTime() {
		mInterpolantComputationTime.start();
	}

	public void stopInterpolantComputationTime() {
		mInterpolantComputationTime.stop();
	}

	public void aggregateTraceCheckStatisticsSkipNotReady(final TraceCheckStatisticsGenerator other) {
		final Map<String, Field> fields = getStatisticFields();
		for (final String key : other.getKeys()) {
			final MeasureDefinition measureDef = getMeasure(key).getMeasureDefinition();
			final Object localValue = getValue(key);
			if (!measureDef.isReady(localValue)) {
				// skip aggregation with local measures that are not ready like running clocks etc.
				// read other value anyway to avoid triggering not-read check
				other.getValue(key);
				continue;
			}
			final Object value = measureDef.aggregate(getValue(key), other.getValue(key));
			final Field field = fields.get(key);
			ReflectionUtil.write(this, field, value);
		}
		other.close();
	}

}