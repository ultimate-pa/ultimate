/*
 * Copyright (C) 2017 Jill Enke (enkei@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

public class FastUPRBenchmark implements ICsvProviderProvider<String> {

	private final Deque<FastUPRRun> mRuns;
	private int mPathsFound;
	private int mPathsTried;
	private int mSuccesses;

	public FastUPRBenchmark() {
		mSuccesses = 0;
		mPathsTried = 0;
		mPathsFound = 0;
		mRuns = new ArrayDeque<>();
	}

	public void startRun(final IcfgLocation loopHead) {
		mRuns.add(new FastUPRRun(loopHead));
	}

	public void endRun(final boolean success) {
		mPathsTried++;
		if (success) {
			mSuccesses++;
		}
		mRuns.getLast().endRun(success);
	}

	public void setPathsFound(final int count) {
		mPathsFound = count;
	}

	static double getNanosecondsToUnit(final long nanoseconds, final TimeUnit unit) {
		switch (unit) {
		case NANOSECONDS:
			return nanoseconds;
		case MICROSECONDS:
			return nanoseconds / 1000.0;
		case MILLISECONDS:
			return nanoseconds / 1000000.0;
		case SECONDS:
			return nanoseconds / 1000000000.0;
		case MINUTES:
			return nanoseconds / 60000000000.0;
		case HOURS:
			return nanoseconds / 3600000000000.0;
		case DAYS:
			return nanoseconds / 86400000000000.0;
		default:
			throw new IllegalArgumentException();
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder("Benchmark Results are:\n");
		sb.append(createCsvProvider().toString());
		sb.append(" * FastUPR found: " + mPathsFound + " loopPaths and tried to accelerate " + mPathsTried + ".\n");
		sb.append(" * FastUPR accelerated " + mSuccesses + "/" + mPathsTried + " paths.");
		return sb.toString();
	}

	@Override
	public ICsvProvider<String> createCsvProvider() {
		final List<String> colHeaders = new ArrayList<>();
		colHeaders.add("Success");
		colHeaders.add(" Time elapsed ");
		final SimpleCsvProvider<String> prov = new SimpleCsvProvider<>(colHeaders);
		for (final FastUPRRun run : mRuns) {
			final List<String> values = new ArrayList<>();
			values.add(run.mSuccessful ? "TRUE" : "FALSE");
			values.add(new StringBuilder().append(
					Math.round(100.0 * FastUPRBenchmark.getNanosecondsToUnit(run.mTimeElapsed, TimeUnit.MILLISECONDS))
							/ 100.0)
					.toString());
			prov.addRow(run.mLoopHead.toString(), values);
		}
		return prov;
	}

	private static final class FastUPRRun {
		public boolean mSuccessful;
		public final IcfgLocation mLoopHead;
		public long mTimeElapsed;
		private final long mStartTime;

		FastUPRRun(final IcfgLocation head) {
			mLoopHead = head;
			mStartTime = System.nanoTime();
		}

		public void endRun(final boolean success) {
			mSuccessful = success;
			mTimeElapsed = System.nanoTime() - mStartTime;
		}

		@Override
		public String toString() {
			final StringBuilder sb = new StringBuilder("Loop Head:" + mLoopHead.toString() + ", ");
			sb.append("Success: " + mSuccessful + ", ");
			sb.append("Time elapsed: "
					+ Math.round(100.0 * FastUPRBenchmark.getNanosecondsToUnit(mTimeElapsed, TimeUnit.MILLISECONDS))
							/ 100.0);
			return sb.toString();
		}
	}
}
