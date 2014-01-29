package de.uni_freiburg.informatik.ultimate.util;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;

import org.apache.log4j.Logger;

/**
 * 
 * This class should provide timing functions to measure runtime and perhaps
 * other aspects of tool and parser performance
 * 
 * still under construction
 * 
 * @author dietsch
 * 
 */
public class Benchmark {

	// long heapSize = Runtime.getRuntime().totalMemory();
	//
	// long heapFreeSize = Runtime.getRuntime().freeMemory();
	//
	// long heapMaxSize = Runtime.getRuntime().maxMemory();
	//
	// logger.info(String.format(
	// "Statistics: heapSize=%s heapFreeSize=%s heapMaxSize=%s",
	// humanReadableByteCount(heapSize, true),
	// humanReadableByteCount(heapFreeSize, true),
	// humanReadableByteCount(heapMaxSize, true)));

	private long mStartTime;

	// Get current size of heap in bytes
	private long mStartHeapSize;

	// Get amount of free memory within the heap in bytes. This size will
	// increase after garbage collection and decrease as new objects are
	// created.
	private long mStartHeapFreeSize;

	// Get maximum size of heap in bytes. The heap cannot grow beyond this
	// size. Any attempt will result in an OutOfMemoryException.
	private long mMaxHeapSize;

	private int mCurrentIndex;
	private HashMap<String, Watch> mWatches;
	private Logger mLogger;

	public Benchmark() {
		mLogger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
		reset();
	}

	public void register(String title) {
		if (!mWatches.containsKey(title)) {
			mWatches.put(title, new Watch(title, mCurrentIndex++));
		}
	}

	public void unregister(String title) {
		mWatches.remove(title);
	}

	public void start(String title) {
		Watch watch = mWatches.get(title);
		if (watch == null) {
			watch = new Watch(title, mCurrentIndex++);
			mWatches.put(title, watch);
		}
		watch.mStartHeapSize = Runtime.getRuntime().totalMemory();
		watch.mStartHeapFreeSize = Runtime.getRuntime().freeMemory();
		watch.mStartTime = System.nanoTime();
	}

	public void startAll() {
		mStartTime = System.nanoTime();
		mStartHeapSize = Runtime.getRuntime().totalMemory();
		mStartHeapFreeSize = Runtime.getRuntime().freeMemory();
	}

	public void stop(String title) {
		long stopDate = System.nanoTime();
		long stopHeapSize = Runtime.getRuntime().totalMemory();
		long stopHeapFreeSize = Runtime.getRuntime().freeMemory();
		stopWatch(title, stopDate, stopHeapSize, stopHeapFreeSize);
	}

	public void stopAll() {
		long stopDate = System.nanoTime();
		long stopHeapSize = Runtime.getRuntime().totalMemory();
		long stopHeapFreeSize = Runtime.getRuntime().freeMemory();
		for (String key : mWatches.keySet()) {
			stopWatch(key, stopDate, stopHeapSize, stopHeapFreeSize);
		}
	}

	private void stopWatch(String title, long stopDate, long stopHeapSize, long stopHeapFreeSize) {
		Watch watch = mWatches.get(title);
		if (watch == null) {
			return;
		}

		if (watch.mStartTime == -1 && mStartTime == -1) {
			return;
		}

		if (watch.mStartTime == -1) {
			// this watch was started via startAll
			watch.mElapsedTime = stopDate - mStartTime;
			watch.mStartHeapSize = mStartHeapSize;
			watch.mStartHeapFreeSize = mStartHeapFreeSize;
		} else {
			// this watch was started via start(title)
			watch.mElapsedTime = stopDate - watch.mStartTime;
		}

		watch.mStopHeapSize = stopHeapSize;
		watch.mStopHeapFreeSize = stopHeapFreeSize;

	}

	public void reset() {
		mStartTime = -1;
		mStartHeapSize = -1;
		mStartHeapFreeSize = -1;
		mMaxHeapSize = Runtime.getRuntime().maxMemory();
		mCurrentIndex = 0;
		mWatches = new HashMap<String, Watch>();
	}

	public void report() {
		ArrayList<Watch> sortedWatches = new ArrayList<Watch>(mWatches.values());
		Collections.sort(sortedWatches, new Comparator<Watch>() {
			@Override
			public int compare(Watch o1, Watch o2) {
				return Integer.compare(o1.mIndex, o2.mIndex);
			}
		});

		for (Watch s : sortedWatches) {
			mLogger.info(s);
		}
	}

	public double getElapsedTime(String title, TimeUnit unit) {
		Watch watch = mWatches.get(title);
		if (watch == null) {
			return -1;
		} else {
			return getNanosecondsToUnit(watch.mElapsedTime, unit);
		}
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

	private class Watch {

		private String mTitle;
		private int mIndex;

		private long mStartTime;
		private long mElapsedTime;

		private long mStartHeapSize;
		private long mStopHeapSize;

		private long mStartHeapFreeSize;
		private long mStopHeapFreeSize;

		private Watch(String title, int index) {
			mTitle = title;
			mIndex = index;

			mStartTime = -1;
			mElapsedTime = -1;

			mStartHeapSize = -1;
			mStartHeapFreeSize = -1;

			mStopHeapSize = -1;
			mStopHeapFreeSize = -1;

		}

		@Override
		public String toString() {
			return toString(TimeUnit.MILLISECONDS, 2);
		}

		public String toString(TimeUnit timeUnit, int decimals) {
			if (mElapsedTime == -1) {
				return String.format("%s was not measured", mTitle);
			}

			long heapDelta = mStopHeapSize - mStartHeapSize;
			long freeDelta = mStartHeapFreeSize - mStopHeapFreeSize;
			String prefix = freeDelta < 0 ? "-" : "";
			freeDelta = Math.abs(freeDelta);

			if (heapDelta == 0) {

				return String.format("%s took %." + decimals
						+ "f %s. It used %s%s heap space. Currently, %s are free. Max. heap size is %s.", mTitle,
						getNanosecondsToUnit(mElapsedTime, timeUnit), getUnitString(timeUnit), prefix,
						Utils.humanReadableByteCount(freeDelta, true),
						Utils.humanReadableByteCount(mStopHeapFreeSize, true),
						Utils.humanReadableByteCount(mMaxHeapSize, true));

			} else {
				return String
						.format("%s took %."
								+ decimals
								+ "f %s. The heap size changed %s, it used %s heap space and currently, %s are free. Max. heap size is %s.",
								mTitle, getNanosecondsToUnit(mElapsedTime, timeUnit), getUnitString(timeUnit),
								Utils.humanReadableByteCount(heapDelta, true), prefix,
								Utils.humanReadableByteCount(freeDelta, true),
								Utils.humanReadableByteCount(mStopHeapFreeSize, true),
								Utils.humanReadableByteCount(mMaxHeapSize, true));

			}

		}

	}
}
