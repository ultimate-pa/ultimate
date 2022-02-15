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
package de.uni_freiburg.informatik.ultimate.util.statistics.measures;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
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
	private long mMaxMemorySizeBytes;

	private Map<String, TimeMemoryTracker> mWatches;
	private TimeMemoryTracker mGlobalWatch;

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
			mWatches.put(title, new TimeMemoryTracker(title, mMaxMemorySizeBytes));
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
		final TimeMemoryTracker watch =
				mWatches.computeIfAbsent(title, a -> new TimeMemoryTracker(a, mMaxMemorySizeBytes));
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
		final TimeMemoryTracker watch = mWatches.get(title);
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
		final TimeMemoryTracker watch = mWatches.get(title);
		if (watch == null) {
			return;
		}
		watch.start();
	}

	/**
	 * Resets the benchmark object and clears all watches.
	 */
	public void reset() {
		mMaxMemorySizeBytes = Runtime.getRuntime().maxMemory();
		mGlobalWatch = new TimeMemoryTracker("Global", mMaxMemorySizeBytes);
		mWatches = new LinkedHashMap<>();
	}

	public void printResult(final ILogger logger) {
		for (final TimeMemoryTracker s : mWatches.values()) {
			logger.info(s);
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		final String lineSeparator = System.getProperty("line.separator");
		sb.append("Benchmark results are:").append(lineSeparator);
		for (final TimeMemoryTracker s : mWatches.values()) {
			sb.append(" * ").append(s).append(lineSeparator);
		}
		sb.delete(sb.length() - lineSeparator.length(), sb.length());
		return sb.toString();
	}

	public String getReportString(final String title) {
		final TimeMemoryTracker watch = mWatches.get(title);
		if (watch == null) {
			return "";
		}
		return watch.toString();
	}

	public double getElapsedTime(final String title, final TimeUnit unit) {
		final TimeMemoryTracker watch = mWatches.get(title);
		if (watch == null) {
			return -1;
		}
		return CoreUtil.convertTimeUnit(watch.mElapsedTimeNs, TimeUnit.NANOSECONDS, unit);
	}

	public long getStartHeapSize(final String title) {
		final TimeMemoryTracker watch = mWatches.get(title);
		if (watch == null) {
			return -1;
		}
		return watch.mStartMemorySizeBytes;
	}

	public long getStopHeapSize(final String title) {
		final TimeMemoryTracker watch = mWatches.get(title);
		if (watch == null) {
			return -1;
		}
		return watch.mStopMemorySizeBytes;
	}

	public long getStartMemoryFreeSize(final String title) {
		final TimeMemoryTracker watch = mWatches.get(title);
		if (watch == null) {
			return -1;
		}
		return watch.mStartMemoryFreeSizeBytes;
	}

	public long getStopMemoryFreeSize(final String title) {
		final TimeMemoryTracker watch = mWatches.get(title);
		if (watch == null) {
			return -1;
		}
		return watch.mStopMemoryFreeSizeBytes;
	}

	public long getPeakMemoryConsumed(final String title) {
		final TimeMemoryTracker watch = mWatches.get(title);
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
		for (final TimeMemoryTracker w : mWatches.values()) {
			rtr.add(w.mTitle);
		}
		return rtr;
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
		case "CodeHeap 'non-nmethods'":
		case "CodeHeap 'profiled nmethods'":
		case "CodeHeap 'non-profiled nmethods'":
			return false;
		case "G1 Eden Space":
		case "G1 Old Gen":
		case "G1 Survivor Space":
		case "Eden Space":
		case "PS Eden Space":
		case "PS Survivor Space":
		case "Survivor Space":
		case "PS Old Gen":
		case "Tenured Gen":
			return true;
		default:
			throw new IllegalArgumentException("Unknown memory pool name \"" + memoryPoolName + "\"");
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

		for (final TimeMemoryTracker w : mWatches.values()) {

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
