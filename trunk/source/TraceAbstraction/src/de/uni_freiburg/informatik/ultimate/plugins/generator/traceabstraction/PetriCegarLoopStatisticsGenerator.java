/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil.Reflected;
import de.uni_freiburg.informatik.ultimate.util.statistics.BaseStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.DefaultMeasureDefinitions;
import de.uni_freiburg.informatik.ultimate.util.statistics.measures.TimeTracker;

public class PetriCegarLoopStatisticsGenerator extends BaseStatisticsDataProvider {

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mFlowIncreaseByBackfolding;

	@Reflected(prettyName = "BasicCegarLoop")
	@Statistics(type = DefaultMeasureDefinitions.STATISTICS_CONVERT_AGGREGATE)
	private final CegarLoopStatisticsGenerator mCegarLoopStatisticsGenerator;

	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mBackfoldingTime = new TimeTracker();

	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mBackfoldingUnfoldingTime = new TimeTracker();

	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mEmptinessCheckTime = new TimeTracker();

	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mRemoveRedundantFlowTime = new TimeTracker();

	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mRemoveRedundantFlowUnfoldingTime = new TimeTracker();

	public PetriCegarLoopStatisticsGenerator(final IToolchainStorage storage,
			final CegarLoopStatisticsGenerator cegarLoopStatisticsGenerator) {
		super(storage);
		mCegarLoopStatisticsGenerator = cegarLoopStatisticsGenerator;
	}

	public void reportFlowIncreaseByBackfolding(final int flowIncrease) {
		mFlowIncreaseByBackfolding += flowIncrease;
	}

	public void startBackfoldingTime() {
		mBackfoldingTime.start();
	}

	public void stopBackfoldingTime() {
		mBackfoldingTime.stop();
	}

	public void startBackfoldingUnfoldingTime() {
		mBackfoldingUnfoldingTime.start();
	}

	public void stopBackfoldingUnfoldingTime() {
		mBackfoldingUnfoldingTime.stop();
	}

	public void startEmptinessCheckTime() {
		mEmptinessCheckTime.start();
	}

	public void stopEmptinessCheckTime() {
		mEmptinessCheckTime.stop();
	}

	public void startRemoveRedundantFlowTime() {
		mRemoveRedundantFlowTime.start();
	}

	public void stopRemoveRedundantFlowTime() {
		mRemoveRedundantFlowTime.stop();
	}

	public void startRemoveRedundantFlowUnfoldingTime() {
		mRemoveRedundantFlowUnfoldingTime.start();
	}

	public void stopRemoveRedundantFlowUnfoldingTime() {
		mRemoveRedundantFlowUnfoldingTime.stop();
	}

}
