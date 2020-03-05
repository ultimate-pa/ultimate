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

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsGeneratorWithStopwatches;

public class PetriCegarLoopStatisticsGenerator extends StatisticsGeneratorWithStopwatches
		implements IStatisticsDataProvider {

	private int mFlowIncreaseByBackfolding = 0;
	private final CegarLoopStatisticsGenerator mCegarLoopStatisticsGenerator;

	public PetriCegarLoopStatisticsGenerator(final CegarLoopStatisticsGenerator cegarLoopStatisticsGenerator) {
		super();
		mCegarLoopStatisticsGenerator = cegarLoopStatisticsGenerator;
	}

	@Override
	public Collection<String> getKeys() {
		return getBenchmarkType().getKeys();
	}

	public void reportFlowIncreaseByBackfolding(final int flowIncrease) {
		mFlowIncreaseByBackfolding += flowIncrease;
	}

	@Override
	public Object getValue(final String key) {
		final PetriCegarLoopStatisticsDefinitions keyEnum = Enum.valueOf(PetriCegarLoopStatisticsDefinitions.class,
				key);
		switch (keyEnum) {
		case BackfoldingTime:
		case BackfoldingUnfoldingTime:
		case EmptinessCheckTime:
		case RemoveRedundantFlowTime:
		case RemoveRedundantFlowUnfoldingTime:
			try {
				return getElapsedTime(key);
			} catch (final StopwatchStillRunningException e) {
				throw new AssertionError("clock still running: " + key);
			}
		case FlowIncreaseByBackfolding:
			return mFlowIncreaseByBackfolding;
		case BasicCegarLoop:
			final StatisticsData result = new StatisticsData();
			result.aggregateBenchmarkData(mCegarLoopStatisticsGenerator);
			return result;
		default:
			throw new AssertionError("unknown data");
		}
	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return PetriCegarStatisticsType.getInstance();
	}

	@Override
	public String[] getStopwatches() {
		return new String[] { PetriCegarLoopStatisticsDefinitions.BackfoldingTime.toString(),
				PetriCegarLoopStatisticsDefinitions.BackfoldingUnfoldingTime.toString(),
				PetriCegarLoopStatisticsDefinitions.EmptinessCheckTime.toString(),
				PetriCegarLoopStatisticsDefinitions.RemoveRedundantFlowTime.toString(),
				PetriCegarLoopStatisticsDefinitions.RemoveRedundantFlowUnfoldingTime.toString(), };
	}
}
