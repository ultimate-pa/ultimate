/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck;

import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ContainsQuantifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUtils.FormulaSize;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsGeneratorWithStopwatches;

public class TraceCheckStatisticsGenerator extends StatisticsGeneratorWithStopwatches
		implements IStatisticsDataProvider {

	public enum InterpolantType {
		Craig, Forward, Backward
	}

	private int mNumberOfCodeBlocks = 0;
	private int mNumberOfCodeBlocksAsserted = 0;
	private int mNumberOfCheckSat = 0;
	private int mConstructedInterpolants = 0;
	private int mQuantifiedInterpolants = 0;
	private long mSizeOfPredicates = 0;
	private int mNumberOfNonLiveVariables = 0;
	private int mConjunctsInSsa = 0;
	private int mConjunctsInUnsatCore = 0;
	private int mInterpolantComputations = 0;
	private int mPerfectInterpolantSequences = 0;
	private BackwardCoveringInformation mInterpolantCoveringCapability = new BackwardCoveringInformation(0, 0);

	private final boolean mCollectInterpolatSequenceStatistics;

	public TraceCheckStatisticsGenerator(final boolean collectInterpolatSequenceStatistics) {
		mCollectInterpolatSequenceStatistics = collectInterpolatSequenceStatistics;
	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return TraceCheckStatisticsType.getInstance();
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
			final boolean isQuantified = new ContainsQuantifier().containsQuantifier(pred.getFormula());
			if (isQuantified) {
				mQuantifiedInterpolants++;
			}
			mSizeOfPredicates += computeLongSumOfIntArray(
					PredicateUtils.computeDagSizeOfPredicates(interpolants, FormulaSize.TREESIZE));
		}
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

	@Override
	public Object getValue(final String key) {
		final TraceCheckStatisticsDefinitions keyEnum = Enum.valueOf(TraceCheckStatisticsDefinitions.class, key);
		switch (keyEnum) {
		case SsaConstructionTime:
		case SatisfiabilityAnalysisTime:
		case InterpolantComputationTime:
			try {
				return getElapsedTime(key);
			} catch (final StopwatchStillRunningException e) {
				throw new AssertionError("clock still running: " + key);
			}
		case NumberOfCodeBlocks:
			return mNumberOfCodeBlocks;
		case NumberOfCodeBlocksAsserted:
			return mNumberOfCodeBlocksAsserted;
		case NumberOfCheckSat:
			return mNumberOfCheckSat;
		case ConstructedInterpolants:
			return mConstructedInterpolants;
		case QuantifiedInterpolants:
			return mQuantifiedInterpolants;
		case SizeOfPredicates:
			return mSizeOfPredicates;
		case NumberOfNonLiveVariables:
			return mNumberOfNonLiveVariables;
		case ConjunctsInSsa:
			return mConjunctsInSsa;
		case ConjunctsInUnsatCore:
			return mConjunctsInUnsatCore;
		case InterpolantComputations:
			return mInterpolantComputations;
		case PerfectInterpolantSequences:
			return mPerfectInterpolantSequences;
		case InterpolantCoveringCapability:
			return mInterpolantCoveringCapability;
		default:
			throw new AssertionError("unknown data");
		}
	}

	@Override
	public String[] getStopwatches() {
		return new String[] { TraceCheckStatisticsDefinitions.SsaConstructionTime.toString(),
				TraceCheckStatisticsDefinitions.SatisfiabilityAnalysisTime.toString(),
				TraceCheckStatisticsDefinitions.InterpolantComputationTime.toString() };
	}

	@Override
	public Collection<String> getKeys() {
		return TraceCheckStatisticsType.getInstance().getKeys();
	}

	public boolean isCollectingInterpolantSequenceStatistics() {
		return mCollectInterpolatSequenceStatistics;
	}

}