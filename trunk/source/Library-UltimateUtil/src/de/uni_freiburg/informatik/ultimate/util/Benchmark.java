package de.uni_freiburg.informatik.ultimate.util;

import java.lang.management.ManagementFactory;
import java.lang.management.MemoryPoolMXBean;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.concurrent.TimeUnit;

import org.apache.log4j.LogManager;
import org.apache.log4j.Logger;

/**
 * This class provides functions to measure runtime and memory consumption
 * 
 * @author dietsch
 * 
 */
public class Benchmark {

	// Get maximum size of heap in bytes. The heap cannot grow beyond this
	// size. Any attempt will result in an OutOfMemoryException.
	private long mMaxMemorySize;

	private int mCurrentIndex;
	private HashMap<String, Watch> mWatches;

	private Logger mLogger;
	private Watch mGlobalWatch;

	public Benchmark() {
		mLogger = LogManager.getLogger(getClass());
		reset();
	}

	/**
	 * Register a new watch, but do not start it. Useful for starting many
	 * watches at the same time with {@link #startAll()}, and then stopping them
	 * separately.
	 * 
	 * @param title
	 *            The title of the watch to register. Titles have to be unique
	 *            and non-null.
	 */
	public void register(String title) {
		if (!mWatches.containsKey(title)) {
			mWatches.put(title, new Watch(title, mCurrentIndex++));
		}
	}

	/**
	 * Unregisters a specific watch.
	 * 
	 * @param title
	 *            The title of the watch to unregister. If the watch does not
	 *            exist, this method will do nothing.
	 */
	public void unregister(String title) {
		mWatches.remove(title);
	}

	/**
	 * Starts a specific watch. Starting means taking the starting time and the
	 * various heap sizes. If the watch is not already registered, it will be
	 * afterwards.
	 * 
	 * @param title
	 *            The title of the watch to register. Titles have to be unique
	 *            and non-null. If the watch did not exists previously, it will
	 *            be registered automatically.
	 */
	public void start(String title) {
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

	public void stop(String title) {
		stopInternal(title, System.nanoTime());
	}

	public void stopAll() {
		long stopTime = System.nanoTime();

		for (String key : mWatches.keySet()) {
			stopInternal(key, stopTime);
		}
	}

	private void stopInternal(String title, long stopTime) {
		Watch watch = mWatches.get(title);
		if (watch == null) {
			return;
		}

		if (watch.mStartTime == -1 && mGlobalWatch.mStartTime == -1) {
			return;
		}

		if (watch.mStartTime == -1) {
			// this watch was started via startAll
			watch.mStartTime = mGlobalWatch.mStartTime;
			watch.mStartMemorySize = mGlobalWatch.mStartMemorySize;
			watch.mStartMemoryFreeSize = mGlobalWatch.mStartMemoryFreeSize;
			watch.mStartPeakMemorySize = mGlobalWatch.mStartPeakMemorySize;
		}
		watch.stop(stopTime);
	}

	public void pause(String title) {
		stop(title);
	}

	public void unpause(String title) {
		Watch watch = mWatches.get(title);
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
		mMaxMemorySize = Runtime.getRuntime().maxMemory();
		mWatches = new HashMap<String, Watch>();
	}

	public void report() {
		for (Watch s : getSortedWatches()) {
			mLogger.info(s);
		}
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		String lineSeparator = System.getProperty("line.separator");
		sb.append("Benchmark results are:").append(lineSeparator);
		for (Watch s : getSortedWatches()) {
			sb.append(" * ").append(s).append(lineSeparator);
		}
		sb.delete(sb.length()-lineSeparator.length(), sb.length());
		return sb.toString();
	}
	
	private Collection<Watch> getSortedWatches(){
		ArrayList<Watch> sortedWatches = new ArrayList<Watch>(mWatches.values());
		Collections.sort(sortedWatches, new Comparator<Watch>() {
			@Override
			public int compare(Watch o1, Watch o2) {

				return Integer.compare(o1.mIndex, o2.mIndex);
			}
		});
		return sortedWatches;
	}

	public String getReportString(String title) {
		Watch watch = mWatches.get(title);
		if (watch == null) {
			return "";
		}
		return watch.toString();
	}

	public double getElapsedTime(String title, TimeUnit unit) {
		Watch watch = mWatches.get(title);
		if (watch == null) {
			return -1;
		} else {
			return getNanosecondsToUnit(watch.mElapsedTime, unit);
		}
	}

	public long getStartHeapSize(String title) {
		Watch watch = mWatches.get(title);
		if (watch == null) {
			return -1;
		} else {
			return watch.mStartMemorySize;
		}
	}

	public long getStopHeapSize(String title) {
		Watch watch = mWatches.get(title);
		if (watch == null) {
			return -1;
		} else {
			return watch.mStopMemorySize;
		}
	}

	public long getStartMemoryFreeSize(String title) {
		Watch watch = mWatches.get(title);
		if (watch == null) {
			return -1;
		} else {
			return watch.mStartMemoryFreeSize;
		}
	}

	public long getStopMemoryFreeSize(String title) {
		Watch watch = mWatches.get(title);
		if (watch == null) {
			return -1;
		} else {
			return watch.mStopMemoryFreeSize;
		}
	}

	public long getPeakMemoryConsumed(String title) {
		Watch watch = mWatches.get(title);
		if (watch == null) {
			return -1;
		} else {
			return watch.mPeakMemorySize - watch.mStartPeakMemorySize;
		}
	}

	public long getMaxHeapSize(String title) {
		return mMaxMemorySize;
	}

	public List<String> getTitles() {
		ArrayList<String> rtr = new ArrayList<String>();
		for (Watch w : mWatches.values()) {
			rtr.add(w.mTitle);
		}
		return rtr;
	}

	private String getUnitString(TimeUnit unit) {
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

	private double getNanosecondsToUnit(long nanoseconds, TimeUnit unit) {
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

	private boolean isHeap(String memoryPoolName) {
		switch (memoryPoolName) {
		case "Code Cache":
		case "PS Perm Gen":
			return false;
		case "PS Eden Space":
		case "PS Survivor Space":
		case "PS Old Gen":
			return true;
		}
		throw new IllegalArgumentException();
	}

	private class Watch {

		private String mTitle;
		private int mIndex;

		private long mStartTime;
		private long mElapsedTime;

		private long mStartMemorySize;
		private long mStopMemorySize;

		private long mStartMemoryFreeSize;
		private long mStopMemoryFreeSize;

		private long mStartPeakMemorySize;
		private long mPeakMemorySize;

		private List<MemoryPoolMXBean> mMemoryPoolBeans;

		private Watch(String title, int index) {
			mTitle = title;
			mIndex = index;
			mMemoryPoolBeans = ManagementFactory.getMemoryPoolMXBeans();
			reset();
		}

		private void start() {
			mStartMemorySize = Runtime.getRuntime().totalMemory();
			mStartMemoryFreeSize = Runtime.getRuntime().freeMemory();

			long startMemoryUsage = 0;
			for (MemoryPoolMXBean bean : mMemoryPoolBeans) {
				bean.resetPeakUsage();
				if (isHeap(bean.getName())) {
					startMemoryUsage = startMemoryUsage + bean.getPeakUsage().getUsed();
				}
			}
			mStartPeakMemorySize = startMemoryUsage;
			mStartTime = System.nanoTime();
		}

		private void stop(long stopTime) {
			mElapsedTime = stopTime - mStartTime + mElapsedTime;
			mStopMemorySize = Runtime.getRuntime().totalMemory();
			mStopMemoryFreeSize = Runtime.getRuntime().freeMemory();

			long stopMemoryUsage = 0;
			for (MemoryPoolMXBean bean : mMemoryPoolBeans) {
				if (isHeap(bean.getName())) {
					stopMemoryUsage = stopMemoryUsage + bean.getPeakUsage().getUsed();
				}
			}
			mPeakMemorySize = Math.max(mPeakMemorySize, Math.max(stopMemoryUsage, mStartPeakMemorySize));
		}

		private void reset() {
			mStartTime = -1;
			mElapsedTime = 0;

			mStartMemorySize = 0;
			mStartMemoryFreeSize = 0;

			mStopMemorySize = 0;
			mStopMemoryFreeSize = 0;

			mStartPeakMemorySize = 0;
			mPeakMemorySize = 0;
		}

		@Override
		public String toString() {
			return toString(TimeUnit.MILLISECONDS, 2);
		}

		public String toString(TimeUnit timeUnit, int decimals) {
			if (mStartTime == -1) {
				return String.format("%s was not measured", mTitle);
			}

			long memoryDelta = mStopMemorySize - mStartMemorySize;
			long freeMemoryDelta = mStartMemoryFreeSize - mStopMemoryFreeSize;
			String freeMemoryDeltaPrefix = freeMemoryDelta < 0 ? "-" : "";
			freeMemoryDelta = Math.abs(freeMemoryDelta);

			long peakMemoryDelta = mPeakMemorySize - mStartPeakMemorySize;
			String peakMemoryDeltaPrefix = peakMemoryDelta < 0 ? "-" : "";
			peakMemoryDelta = Math.abs(peakMemoryDelta);

			StringBuilder sb = new StringBuilder();

			sb.append(String.format("%s took %." + decimals + "f %s.", mTitle,
					getNanosecondsToUnit(mElapsedTime, timeUnit), getUnitString(timeUnit)));

			if (memoryDelta != 0) {
				String heapPrefix = memoryDelta < 0 ? "-" : "";
				memoryDelta = Math.abs(memoryDelta);
				sb.append(String.format(" Allocated memory was %s in the beginning and %s in the end (delta: %s%s).",
						Utils.humanReadableByteCount(mStartMemorySize, true),
						Utils.humanReadableByteCount(mStopMemorySize, true), heapPrefix,
						Utils.humanReadableByteCount(memoryDelta, true)));
			} else {
				sb.append(String.format(" Allocated memory is still %s.",
						Utils.humanReadableByteCount(mStartMemorySize, true)));
			}

			if (freeMemoryDelta != 0) {
				sb.append(String.format(" Free memory was %s in the beginning and %s in the end (delta: %s%s).",
						Utils.humanReadableByteCount(mStartMemoryFreeSize, true),
						Utils.humanReadableByteCount(mStopMemoryFreeSize, true), freeMemoryDeltaPrefix,
						Utils.humanReadableByteCount(freeMemoryDelta, true)));
			} else {
				sb.append(String.format(" Free memory is still %s.",
						Utils.humanReadableByteCount(mStartMemoryFreeSize, true)));
			}

			if (peakMemoryDelta != 0) {
				sb.append(String.format(" Peak memory consumption was %s%s.", peakMemoryDeltaPrefix,
						Utils.humanReadableByteCount(peakMemoryDelta, true)));
			} else {
				sb.append(" There was no memory consumed.");
			}

			sb.append(String.format(" Max. memory is %s", Utils.humanReadableByteCount(mMaxMemorySize, true)));
			return sb.toString();

		}

	}
}
