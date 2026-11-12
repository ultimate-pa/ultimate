/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel;

import java.lang.management.ManagementFactory;
import java.lang.management.MemoryPoolMXBean;
import java.lang.management.MemoryType;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Retires workers of {@link ParallelNwaCegarLoop} when the heap fills up, so that k-induction, the one worker that
 * never retires, gets the memory. When the live heap reaches the TA threshold, a TA worker retires, and so on until no
 * TA worker is left. Every worker
 * the watchdog may retire runs under a {@link RetirementTimer}, which stops whatever it runs.
 * <p>
 * The live heap is what a full garbage collection leaves. Forcing one is expensive, so the watchdog first looks at the
 * old generation, which only grows when objects survive young collections (or are too large for them): the garbage
 * that the workers churn through in the young generation does not count there. As long as the old generation is below
 * a threshold, nothing is to be done; only above it does the watchdog collect to confirm, at most once every
 * {@link #MIN_GC_INTERVAL_NANOS}. A collection that finds less live heap than the threshold empties the old
 * generation of its garbage, so the next one comes only once enough objects survived again. (What the memory pools
 * report as left by the last collection is no help: G1 updates it for the old generation only after a mixed or full
 * collection, which does not happen while the old generation is small.)
 * <p>
 * After a TA worker retires, the next one retires only once the first has stopped, so that the memory it frees counts
 * first.
 *
 * @author Max Barth (Max.Barth@lmu.de)
 */
public final class HeapWatchdog {

	private static final long POLL_INTERVAL_MILLIS = 500;
	private static final long MIN_GC_INTERVAL_NANOS = 5_000_000_000L;

	private final ILogger mLogger;
	private final int mTaPercent;
	// The old generation: the heap pools that support a usage threshold, which young generation pools never do
	private final List<MemoryPoolMXBean> mOldPools = new ArrayList<>();
	private final ScheduledExecutorService mExec;
	private final List<RetirementTimer> mTaWorkers = new ArrayList<>();
	private long mLastGcNanos;
	private boolean mCollectedBefore;
	private int mCollections;

	/**
	 * @param taPercent
	 *            the live heap, in % of the maximum heap, at which a TA worker retires
	 */
	public HeapWatchdog(final ILogger logger, final int taPercent) {
		mLogger = logger;
		mTaPercent = taPercent;
		for (final MemoryPoolMXBean pool : ManagementFactory.getMemoryPoolMXBeans()) {
			if (pool.getType() == MemoryType.HEAP && pool.isUsageThresholdSupported()) {
				mOldPools.add(pool);
			}
		}
		mExec = Executors.newSingleThreadScheduledExecutor(runnable -> {
			final Thread thread = new Thread(runnable, "Heap Watchdog");
			thread.setDaemon(true);
			return thread;
		});
	}

	/**
	 * @param timer
	 *            the timer of a TA worker; the TA worker added last retires first
	 */
	public void watchTaWorker(final RetirementTimer timer) {
		mTaWorkers.add(timer);
	}

	public void start() {
		mLogger.info("Heap watchdog: a TA worker retires at %d%% of the %d MB max heap", mTaPercent,
				Runtime.getRuntime().maxMemory() >> 20);
		mExec.scheduleWithFixedDelay(this::check, POLL_INTERVAL_MILLIS, POLL_INTERVAL_MILLIS, TimeUnit.MILLISECONDS);
	}

	public void stop() {
		mExec.shutdownNow();
	}

	private void check() {
		try {
			final RetirementTimer nextTaWorker = nextTaWorker();
			if (nextTaWorker == null && !taRetirementPending()) {
				mLogger.info("Heap watchdog: nothing left to retire, it stops after %d garbage collection(s)",
						mCollections);
				mExec.shutdown();
				return;
			}
			final long maxHeap = Runtime.getRuntime().maxMemory();
			final long taLimit = nextTaWorker != null ? maxHeap / 100 * mTaPercent : Long.MAX_VALUE;
			if (oldGenerationUsed() < taLimit) {
				return;
			}
			final long now = System.nanoTime();
			if (mCollectedBefore && now - mLastGcNanos < MIN_GC_INTERVAL_NANOS) {
				return;
			}
			System.gc();
			mCollections++;
			mCollectedBefore = true;
			mLastGcNanos = System.nanoTime();
			final long live = usedHeap();
			if (live >= taLimit) {
				nextTaWorker.retire(reason(live, maxHeap, mTaPercent));
				// The retired worker no longer counts as active.
				mLogger.warn("Heap watchdog: retiring a TA worker (%d left after it), %s", activeTaWorkers(),
						nextTaWorker.getReason());
			}
		} catch (final Throwable t) {
			// An exception would end the schedule silently.
			mLogger.error("Heap watchdog crashed, no more workers retire: " + t);
			for (final StackTraceElement element : t.getStackTrace()) {
				mLogger.error("\tat " + element);
			}
			throw t;
		}
	}

	private static String reason(final long live, final long maxHeap, final int percent) {
		return String.format("the live heap reached %d MB, %d%% of the %d MB max heap (threshold %d%%)", live >> 20,
				live * 100 / maxHeap, maxHeap >> 20, percent);
	}

	/**
	 * @return the TA worker to retire next, or null if none is to be retired now: none is left, or the last one retired
	 *         has not stopped yet
	 */
	private RetirementTimer nextTaWorker() {
		if (taRetirementPending()) {
			return null;
		}
		for (int i = mTaWorkers.size() - 1; i >= 0; i--) {
			final RetirementTimer worker = mTaWorkers.get(i);
			if (!worker.isRetired() && !worker.hasStopped()) {
				return worker;
			}
		}
		return null;
	}

	private boolean taRetirementPending() {
		return mTaWorkers.stream().anyMatch(worker -> worker.isRetired() && !worker.hasStopped());
	}

	private long activeTaWorkers() {
		return mTaWorkers.stream().filter(worker -> !worker.isRetired() && !worker.hasStopped()).count();
	}

	/**
	 * @return the used old generation, garbage included; the whole used heap if the collector has no old generation
	 */
	private long oldGenerationUsed() {
		if (mOldPools.isEmpty()) {
			return usedHeap();
		}
		long used = 0;
		for (final MemoryPoolMXBean pool : mOldPools) {
			used += pool.getUsage().getUsed();
		}
		return used;
	}

	private static long usedHeap() {
		final Runtime runtime = Runtime.getRuntime();
		return runtime.totalMemory() - runtime.freeMemory();
	}
}
