package de.uni_freiburg.informatik.ultimate.util;

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
 * 
 * This class provides functions to measure runtime and memory consumption
 * 
 * @author dietsch
 * 
 */
public class Benchmark {

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
		mLogger = LogManager.getLogger(getClass());
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

	public void pause(String title) {
		stop(title);
		Watch watch = mWatches.get(title);
		if (watch == null) {
			return;
		}
		Watch oldWatch = watch.copy();
		if(watch.mPausedWatches == null){
			watch.mPausedWatches = new ArrayList<Watch>();
		}
		watch.mPausedWatches.add(oldWatch);
	}

	public void unpause(String title) {
		Watch watch = mWatches.get(title);
		if (watch == null) {
			return;
		}
		start(title);
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
			watch.mStartTime = mStartTime;
			watch.mStartHeapSize = mStartHeapSize;
			watch.mStartHeapFreeSize = mStartHeapFreeSize;
		} 
		
		watch.mElapsedTime = stopDate - watch.mStartTime + watch.mElapsedTime;
		watch.mStopHeapSize = stopHeapSize;
		watch.mStopHeapFreeSize = stopHeapFreeSize;
	}

	/**
	 * Resets the benchmark object and clears all watches.
	 */
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
	
	public String getReportString(String title){
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
			return watch.mStartHeapSize;
		}
	}

	public long getStopHeapSize(String title) {
		Watch watch = mWatches.get(title);
		if (watch == null) {
			return -1;
		} else {
			return watch.mStopHeapSize;
		}
	}

	public long getStartHeapFreeSize(String title) {
		Watch watch = mWatches.get(title);
		if (watch == null) {
			return -1;
		} else {
			return watch.mStartHeapFreeSize;
		}
	}

	public long getStopHeapFreeSize(String title) {
		Watch watch = mWatches.get(title);
		if (watch == null) {
			return -1;
		} else {
			return watch.mStopHeapFreeSize;
		}
	}

	public long getMaxHeapSize(String title) {
		return mMaxHeapSize;
	}

	public Collection<String> getTitles() {
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

	private class Watch {

		private String mTitle;
		private int mIndex;

		private long mStartTime;
		private long mElapsedTime;

		private long mStartHeapSize;
		private long mStopHeapSize;

		private long mStartHeapFreeSize;
		private long mStopHeapFreeSize;

		private List<Watch> mPausedWatches;

		private Watch(String title, int index) {
			mTitle = title;
			mIndex = index;
			reset();
		}

		private void reset() {
			mStartTime = -1;
			mElapsedTime = 0;

			mStartHeapSize = 0;
			mStartHeapFreeSize = 0;

			mStopHeapSize = 0;
			mStopHeapFreeSize = 0;
		}
		
		private Watch copy(){
			Watch m = new Watch(mTitle, mIndex);
			m.mStartTime = mStartTime ;
			m.mElapsedTime = mElapsedTime;

			m.mStartHeapSize = mStartHeapSize;
			m.mStartHeapFreeSize = mStartHeapFreeSize;

			m.mStopHeapSize = mStopHeapSize;
			m.mStopHeapFreeSize = mStopHeapFreeSize;
			return m;
		}

		@Override
		public String toString() {
			return toString(TimeUnit.MILLISECONDS, 2);
		}

		public String toString(TimeUnit timeUnit, int decimals) {
			if (mStartTime == -1) {
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

				String heapPrefix = heapDelta < 0 ? "-" : "";
				heapDelta = Math.abs(heapDelta);

				return String
						.format("%s took %."
								+ decimals
								+ "f %s. The heap size changed %s%s, it used %s%s heap space and currently, %s are free. Max. heap size is %s.",
								mTitle, getNanosecondsToUnit(mElapsedTime, timeUnit), getUnitString(timeUnit),
								heapPrefix, Utils.humanReadableByteCount(heapDelta, true), prefix,
								Utils.humanReadableByteCount(freeDelta, true),
								Utils.humanReadableByteCount(mStopHeapFreeSize, true),
								Utils.humanReadableByteCount(mMaxHeapSize, true));

			}

		}

	}
}
