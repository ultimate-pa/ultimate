/*
 * Copyright (C) 2020 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE accelerated interpolation library.
 *
 * The ULTIMATE accelerated interpolation library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE accelerated interpolation library  is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE accelerated interpolation library . If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE accelerated interpolation library , or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE accelerated interpolation library library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.benchmark;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.AcceleratedInterpolation;
import de.uni_freiburg.informatik.ultimate.util.statistics.BaseStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.DefaultMeasureDefinitions;
import de.uni_freiburg.informatik.ultimate.util.statistics.measures.TimeTracker;

/**
 * Benchmark for evaluating the performance of the {@link AcceleratedInterpolation} paradigm.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 */
public final class AcceleratedInterpolationBenchmark extends BaseStatisticsDataProvider {

	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mAcceleratedInterpolationCoreTime = new TimeTracker();

	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mAcceleratedInterpolationOverallTime = new TimeTracker();

	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mAcceleratedInterpolationLoopDetectorTime = new TimeTracker();

	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mAcceleratedInterpolationLoopAcceleratorTime = new TimeTracker();

	public AcceleratedInterpolationBenchmark(final IToolchainStorage storage) {
		super(storage);
	}

	public void startOverall() {
		mAcceleratedInterpolationOverallTime.start();
	}

	public void startCore() {
		mAcceleratedInterpolationCoreTime.start();
	}

	public void stopAllStopwatches() {
		mAcceleratedInterpolationOverallTime.stop();
		mAcceleratedInterpolationCoreTime.stop();
	}
}
