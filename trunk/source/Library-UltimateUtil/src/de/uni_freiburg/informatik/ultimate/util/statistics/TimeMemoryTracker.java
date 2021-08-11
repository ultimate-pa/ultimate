/*
 * Copyright (C) 2014-2021 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2021 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.statistics;

import java.lang.management.ManagementFactory;
import java.lang.management.MemoryPoolMXBean;
import java.util.List;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class TimeMemoryTracker {

	long mStartTime;
	long mElapsedTimeNs;

	long mStartMemorySizeBytes;
	long mStopMemorySizeBytes;

	long mStartMemoryFreeSizeBytes;
	long mStopMemoryFreeSizeBytes;

	long mStartPeakMemorySizeBytes;
	long mPeakMemorySizeBytes;

	final String mTitle;
	private final long mMaxMemorySizeBytes;
	private final List<MemoryPoolMXBean> mMemoryPoolBeans;

	public TimeMemoryTracker(final String title) {
		this(title, Runtime.getRuntime().maxMemory());
	}

	public TimeMemoryTracker(final String title, final long maxMemorySizeBytes) {
		mMaxMemorySizeBytes = maxMemorySizeBytes;
		mTitle = title;
		mMemoryPoolBeans = ManagementFactory.getMemoryPoolMXBeans();
		reset();
	}

	public void start() {
		mStartMemorySizeBytes = Runtime.getRuntime().totalMemory();
		mStartMemoryFreeSizeBytes = Runtime.getRuntime().freeMemory();
		long startMemoryUsageBytes = 0;
		for (final MemoryPoolMXBean bean : mMemoryPoolBeans) {
			bean.resetPeakUsage();
			if (Benchmark.isHeap(bean.getName())) {
				startMemoryUsageBytes = startMemoryUsageBytes + bean.getPeakUsage().getUsed();
			}
		}
		mStartPeakMemorySizeBytes = startMemoryUsageBytes;
		mStartTime = System.nanoTime();
	}

	public void stop(final long stopTime) {
		mElapsedTimeNs = stopTime - mStartTime + mElapsedTimeNs;
		mStopMemorySizeBytes = Runtime.getRuntime().totalMemory();
		mStopMemoryFreeSizeBytes = Runtime.getRuntime().freeMemory();

		long stopMemoryUsage = 0;
		for (final MemoryPoolMXBean bean : mMemoryPoolBeans) {
			if (Benchmark.isHeap(bean.getName())) {
				stopMemoryUsage = stopMemoryUsage + bean.getPeakUsage().getUsed();
			}
		}
		mPeakMemorySizeBytes = Math.max(mPeakMemorySizeBytes, Math.max(stopMemoryUsage, mStartPeakMemorySizeBytes));
	}

	public void reset() {
		mStartTime = -1;
		mElapsedTimeNs = 0;

		mStartMemorySizeBytes = 0;
		mStartMemoryFreeSizeBytes = 0;

		mStopMemorySizeBytes = 0;
		mStopMemoryFreeSizeBytes = 0;

		mStartPeakMemorySizeBytes = 0;
		mPeakMemorySizeBytes = 0;
	}

	@Override
	public String toString() {
		return toString(TimeUnit.MILLISECONDS, 2);
	}

	private String toString(final TimeUnit timeUnit, final int decimals) {
		if (mStartTime == -1) {
			return String.format("%s was not measured", mTitle);
		}

		long memoryDelta = mStopMemorySizeBytes - mStartMemorySizeBytes;
		long freeMemoryDelta = mStartMemoryFreeSizeBytes - mStopMemoryFreeSizeBytes;
		final String freeMemoryDeltaPrefix = freeMemoryDelta < 0 ? "-" : "";
		freeMemoryDelta = Math.abs(freeMemoryDelta);

		long peakMemoryDelta = getPeakMemoryDelta();
		final String peakMemoryDeltaPrefix = peakMemoryDelta < 0 ? "-" : "";
		peakMemoryDelta = Math.abs(peakMemoryDelta);

		final StringBuilder sb = new StringBuilder();
		final long nanoseconds = mElapsedTimeNs;

		sb.append(String.format("%s took %." + decimals + "f %s.", mTitle,
				CoreUtil.convertTimeUnit(nanoseconds, TimeUnit.NANOSECONDS, timeUnit), CoreUtil.getTimeUnitSymbol(timeUnit)));

		if (memoryDelta != 0) {
			final String heapPrefix = memoryDelta < 0 ? "-" : "";
			memoryDelta = Math.abs(memoryDelta);
			sb.append(String.format(" Allocated memory was %s in the beginning and %s in the end (delta: %s%s).",
					CoreUtil.humanReadableByteCount(mStartMemorySizeBytes, true),
					CoreUtil.humanReadableByteCount(mStopMemorySizeBytes, true), heapPrefix,
					CoreUtil.humanReadableByteCount(memoryDelta, true)));
		} else {
			sb.append(String.format(" Allocated memory is still %s.",
					CoreUtil.humanReadableByteCount(mStartMemorySizeBytes, true)));
		}

		if (freeMemoryDelta != 0) {
			sb.append(String.format(" Free memory was %s in the beginning and %s in the end (delta: %s%s).",
					CoreUtil.humanReadableByteCount(mStartMemoryFreeSizeBytes, true),
					CoreUtil.humanReadableByteCount(mStopMemoryFreeSizeBytes, true), freeMemoryDeltaPrefix,
					CoreUtil.humanReadableByteCount(freeMemoryDelta, true)));
		} else {
			sb.append(String.format(" Free memory is still %s.",
					CoreUtil.humanReadableByteCount(mStartMemoryFreeSizeBytes, true)));
		}

		if (peakMemoryDelta != 0) {
			sb.append(String.format(" Peak memory consumption was %s%s.", peakMemoryDeltaPrefix,
					CoreUtil.humanReadableByteCount(peakMemoryDelta, true)));
		} else {
			sb.append(" There was no memory consumed.");
		}

		sb.append(String.format(" Max. memory is %s.", CoreUtil.humanReadableByteCount(mMaxMemorySizeBytes, true)));
		return sb.toString();

	}

	public long getPeakMemoryDelta() {
		return mPeakMemorySizeBytes - mStartPeakMemorySizeBytes;
	}

}