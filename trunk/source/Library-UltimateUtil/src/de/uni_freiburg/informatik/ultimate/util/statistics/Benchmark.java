/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

/**
 * This class provides functions to measure runtime and memory consumption
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class Benchmark implements ICsvProviderProvider<Double> {

	// Get maximum size of heap in bytes. The heap cannot grow beyond this
	// size. Any attempt will result in an OutOfMemoryException.
	protected long mMaxMemorySizeBytes;

	private int mCurrentIndex;
	private HashMap<String, Watch> mWatches;

	private Watch mGlobalWatch;

	public Benchmark() {
		reset();
	}

	/**
	 * Register a new watch, but do not start it. Useful for starting many watches at the same time with
	 * {@link #startAll()}, and then stopping them separately.
	 *
	 * @param title
	 *            The title of the watch to register. Titles have to be unique and non-null.
	 */
	public void register(final String title) {
		if (!mWatches.containsKey(title)) {
			mWatches.put(title, new Watch(title, mCurrentIndex++));
		}
	}

	/**
	 * Unregisters a specific watch.
	 *
	 * @param title
	 *            The title of the watch to unregister. If the watch does not exist, this method will do nothing.
	 */
	public void unregister(final String title) {
		mWatches.remove(title);
	}

	/**
	 * Starts a specific watch. Starting means taking the starting time and the various heap sizes. If the watch is not
	 * already registered, it will be afterwards.
	 *
	 * @param title
	 *            The title of the watch to register. Titles have to be unique and non-null. If the watch did not exists
	 *            previously, it will be registered automatically.
	 */
	public void start(final String title) {
		Watch watch = mWatches.get(title);
		if (watch == null) {
			watch = new Watch(title, mCurrentIndex++);
			mWatches.put(title, watch);
		}
		watch.reset();
		watch.start();
	}

	public void startAll() {
		mGlobalWatch.reset();
		mGlobalWatch.start();
	}

	public void stop(final String title) {
		stopInternal(title, System.nanoTime());
	}

	public void stopAll() {
		final long stopTime = System.nanoTime();

		for (final String key : mWatches.keySet()) {
			stopInternal(key, stopTime);
		}
	}

	private void stopInternal(final String title, final long stopTime) {
		final Watch watch = mWatches.get(title);
		if (watch == null) {
			return;
		}

		if (watch.mStartTime == -1 && mGlobalWatch.mStartTime == -1) {
			return;
		}

		if (watch.mStartTime == -1) {
			// this watch was started via startAll
			watch.mStartTime = mGlobalWatch.mStartTime;
			watch.mStartMemorySizeBytes = mGlobalWatch.mStartMemorySizeBytes;
			watch.mStartMemoryFreeSizeBytes = mGlobalWatch.mStartMemoryFreeSizeBytes;
			watch.mStartPeakMemorySizeBytes = mGlobalWatch.mStartPeakMemorySizeBytes;
		}
		watch.stop(stopTime);
	}

	public void pause(final String title) {
		stop(title);
	}

	public void unpause(final String title) {
		final Watch watch = mWatches.get(title);
		if (watch == null) {
			return;
		}
		watch.start();
	}

	/**
	 * Resets the benchmark object and clears all watches.
	 */
	public void reset() {
		mCurrentIndex = 1;
		mGlobalWatch = new Watch("Global", 0);
		mMaxMemorySizeBytes = Runtime.getRuntime().maxMemory();
		mWatches = new HashMap<>();
	}

	public void printResult(final ILogger logger) {
		for (final Watch s : getSortedWatches()) {
			logger.info(s);
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		final String lineSeparator = System.getProperty("line.separator");
		sb.append("Benchmark results are:").append(lineSeparator);
		for (final Watch s : getSortedWatches()) {
			sb.append(" * ").append(s).append(lineSeparator);
		}
		sb.delete(sb.length() - lineSeparator.length(), sb.length());
		return sb.toString();
	}

	private Collection<Watch> getSortedWatches() {
		final ArrayList<Watch> sortedWatches = new ArrayList<>(mWatches.values());
		Collections.sort(sortedWatches, new Comparator<Watch>() {
			@Override
			public int compare(final Watch o1, final Watch o2) {
				return Integer.compare(o1.mIndex, o2.mIndex);
			}
		});
		return sortedWatches;
	}

	public String getReportString(final String title) {
		final Watch watch = mWatches.get(title);
		if (watch == null) {
			return "";
		}
		return watch.toString();
	}

	public double getElapsedTime(final String title, final TimeUnit unit) {
		final Watch watch = mWatches.get(title);
		if (watch == null) {
			return -1;
		}
		return getNanosecondsToUnit(watch.mElapsedTimeNs, unit);
	}

	public long getStartHeapSize(final String title) {
		final Watch watch = mWatches.get(title);
		if (watch == null) {
			return -1;
		}
		return watch.mStartMemorySizeBytes;
	}

	public long getStopHeapSize(final String title) {
		final Watch watch = mWatches.get(title);
		if (watch == null) {
			return -1;
		}
		return watch.mStopMemorySizeBytes;
	}

	public long getStartMemoryFreeSize(final String title) {
		final Watch watch = mWatches.get(title);
		if (watch == null) {
			return -1;
		}
		return watch.mStartMemoryFreeSizeBytes;
	}

	public long getStopMemoryFreeSize(final String title) {
		final Watch watch = mWatches.get(title);
		if (watch == null) {
			return -1;
		}
		return watch.mStopMemoryFreeSizeBytes;
	}

	public long getPeakMemoryConsumed(final String title) {
		final Watch watch = mWatches.get(title);
		if (watch == null) {
			return -1;
		}
		return watch.mPeakMemorySizeBytes - watch.mStartPeakMemorySizeBytes;
	}

	public long getMaxHeapSize(final String title) {
		return mMaxMemorySizeBytes;
	}

	public List<String> getTitles() {
		final ArrayList<String> rtr = new ArrayList<>();
		for (final Watch w : mWatches.values()) {
			rtr.add(w.mTitle);
		}
		return rtr;
	}

	static String getUnitString(final TimeUnit unit) {
		switch (unit) {
		case NANOSECONDS:
			return "ns";
		case MICROSECONDS:
			return "µs";
		case MILLISECONDS:
			return "ms";
		case SECONDS:
			return "s";
		case MINUTES:
			return "m";
		case HOURS:
			return "h";
		case DAYS:
			return "d";
		default:
			throw new IllegalArgumentException();
		}
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

	static boolean isHeap(final String memoryPoolName) {
		switch (memoryPoolName) {
		case "Code Cache":
		case "Perm Gen":
		case "PS Perm Gen":
		case "Perm Gen [shared-ro]":
		case "Perm Gen [shared-rw]":
		case "Metaspace":
		case "Compressed Class Space":
			return false;
		case "Eden Space":
		case "PS Eden Space":
		case "PS Survivor Space":
		case "Survivor Space":
		case "PS Old Gen":
		case "Tenured Gen":
			return true;
		default:
			throw new IllegalArgumentException("Unknown memory pool name " + memoryPoolName);
		}
	}

	private final class Watch {

		final String mTitle;
		final int mIndex;

		long mStartTime;
		long mElapsedTimeNs;

		long mStartMemorySizeBytes;
		long mStopMemorySizeBytes;

		long mStartMemoryFreeSizeBytes;
		long mStopMemoryFreeSizeBytes;

		long mStartPeakMemorySizeBytes;
		long mPeakMemorySizeBytes;

		private final List<MemoryPoolMXBean> mMemoryPoolBeans;

		Watch(final String title, final int index) {
			mTitle = title;
			mIndex = index;
			mMemoryPoolBeans = ManagementFactory.getMemoryPoolMXBeans();
			reset();
		}

		void start() {
			mStartMemorySizeBytes = Runtime.getRuntime().totalMemory();
			mStartMemoryFreeSizeBytes = Runtime.getRuntime().freeMemory();
			long startMemoryUsageBytes = 0;
			for (final MemoryPoolMXBean bean : mMemoryPoolBeans) {
				bean.resetPeakUsage();
				if (isHeap(bean.getName())) {
					startMemoryUsageBytes = startMemoryUsageBytes + bean.getPeakUsage().getUsed();
				}
			}
			mStartPeakMemorySizeBytes = startMemoryUsageBytes;
			mStartTime = System.nanoTime();
		}

		void stop(final long stopTime) {
			mElapsedTimeNs = stopTime - mStartTime + mElapsedTimeNs;
			mStopMemorySizeBytes = Runtime.getRuntime().totalMemory();
			mStopMemoryFreeSizeBytes = Runtime.getRuntime().freeMemory();

			long stopMemoryUsage = 0;
			for (final MemoryPoolMXBean bean : mMemoryPoolBeans) {
				if (isHeap(bean.getName())) {
					stopMemoryUsage = stopMemoryUsage + bean.getPeakUsage().getUsed();
				}
			}
			mPeakMemorySizeBytes = Math.max(mPeakMemorySizeBytes, Math.max(stopMemoryUsage, mStartPeakMemorySizeBytes));
			// Runtime.getRuntime().gc();
		}

		void reset() {
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

		public String toString(final TimeUnit timeUnit, final int decimals) {
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

			sb.append(String.format("%s took %." + decimals + "f %s.", mTitle,
					getNanosecondsToUnit(mElapsedTimeNs, timeUnit), getUnitString(timeUnit)));

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

	@Override
	public ICsvProvider<Double> createCsvProvider() {

		final List<String> columHeaders = new ArrayList<>();
		columHeaders.add("Runtime (ns)");
		columHeaders.add("Peak memory consumption (bytes)");
		columHeaders.add("Allocated memory start (bytes)");
		columHeaders.add("Allocated memory end (bytes)");
		columHeaders.add("Free memory start (bytes)");
		columHeaders.add("Free memory end (bytes)");
		columHeaders.add("Max. memory available (bytes)");

		final SimpleCsvProvider<Double> rtr = new SimpleCsvProvider<>(columHeaders);

		for (final Watch w : getSortedWatches()) {

			final List<Double> values = new ArrayList<>();
			values.add(Double.valueOf(w.mElapsedTimeNs));
			values.add(Double.valueOf(w.getPeakMemoryDelta()));
			values.add(Double.valueOf(w.mStartMemorySizeBytes));
			values.add(Double.valueOf(w.mStopMemorySizeBytes));
			values.add(Double.valueOf(w.mStartMemoryFreeSizeBytes));
			values.add(Double.valueOf(w.mStopMemoryFreeSizeBytes));
			values.add(Double.valueOf(mMaxMemorySizeBytes));
			rtr.addRow(w.mTitle, values);
		}

		return rtr;
	}
}
