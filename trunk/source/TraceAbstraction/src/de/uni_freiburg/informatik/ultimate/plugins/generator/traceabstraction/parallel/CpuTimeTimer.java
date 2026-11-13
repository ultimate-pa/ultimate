/*
 * Copyright (C) 2026 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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

import java.time.Duration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;

/**
 * A timer that expires when this process has used a given amount of CPU time since the timer was created: the CPU time
 * of every thread of the JVM, the garbage collector's included, plus that of the external solvers it started. This is
 * what BenchExec charges a run, unlike the wall time of the timers of the progress monitor, which a solver that waits
 * for a core or a heavily loaded machine stretch.
 * <p>
 * The CPU time of a child process is taken from its process handle while it lives; for a child that is gone, the last
 * value seen counts. So up to one {@link #CHECK_INTERVAL_NANOS} of CPU time of each child that ends is missed. The CPU
 * time is measured at most once per {@link #CHECK_INTERVAL_NANOS} of wall time, since listing the descendants scans the
 * process table, and {@link #continueProcessing()} is called often.
 * <p>
 * The timer has no children: register it with
 * {@link de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService#registerChildTimer}, whose
 * layer creates the children and asks this timer and the parent.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class CpuTimeTimer implements IProgressAwareTimer {

	private static final long CHECK_INTERVAL_NANOS = TimeUnit.MILLISECONDS.toNanos(100);

	private final long mLimitNanos;
	private final long mStartNanos;
	// The last CPU time seen of each living child process
	private final Map<Long, Long> mChildNanos = new HashMap<>();
	// The last CPU time seen of the child processes that ended
	private long mEndedChildNanos;

	private long mLastCheck;
	private volatile long mUsedNanos;

	/**
	 * @param limitMillis
	 *            how much CPU time the process may use from now on, in milliseconds; larger than 0
	 */
	public CpuTimeTimer(final long limitMillis) {
		if (limitMillis <= 0) {
			throw new IllegalArgumentException("CPU time limit must be larger than 0, but is " + limitMillis);
		}
		mLimitNanos = TimeUnit.MILLISECONDS.toNanos(limitMillis);
		mStartNanos = measureCpuNanos();
		mLastCheck = System.nanoTime();
	}

	@Override
	public boolean continueProcessing() {
		return usedNanos() < mLimitNanos;
	}

	@Override
	public long remainingTime() {
		return TimeUnit.NANOSECONDS.toMillis(Math.max(0, mLimitNanos - usedNanos()));
	}

	/**
	 * @return the wall-clock time at which the timer expires if from now on the process uses one core
	 */
	@Override
	public long getDeadline() {
		return System.currentTimeMillis() + remainingTime();
	}

	/**
	 * @return how much CPU time the process used since the timer was created, in milliseconds
	 */
	public long getUsedMillis() {
		return TimeUnit.NANOSECONDS.toMillis(usedNanos());
	}

	@Override
	public IProgressAwareTimer getParent() {
		return null;
	}

	@Override
	public IProgressAwareTimer getChildTimer(final long timeout) {
		throw new UnsupportedOperationException("A CPU time timer has no children, register it as a child timer");
	}

	@Override
	public IProgressAwareTimer getChildTimer(final double percentage) {
		throw new UnsupportedOperationException("A CPU time timer has no children, register it as a child timer");
	}

	@Override
	public IProgressAwareTimer getTimer(final long timeout) {
		throw new UnsupportedOperationException("A CPU time timer creates no timers");
	}

	private long usedNanos() {
		final long now = System.nanoTime();
		synchronized (this) {
			if (now - mLastCheck >= CHECK_INTERVAL_NANOS) {
				mLastCheck = now;
				mUsedNanos = measureCpuNanos() - mStartNanos;
			}
		}
		return mUsedNanos;
	}

	/**
	 * @return the CPU time of the JVM and of every child process it started so far, in nanoseconds
	 */
	private synchronized long measureCpuNanos() {
		final ProcessHandle self = ProcessHandle.current();
		final long own = self.info().totalCpuDuration().orElseThrow(
				() -> new UnsupportedOperationException("The OS does not report the CPU time of this process"))
				.toNanos();
		final Set<Long> alive = new HashSet<>();
		self.descendants().forEach(child -> {
			alive.add(child.pid());
			child.info().totalCpuDuration().map(Duration::toNanos)
					.ifPresent(nanos -> mChildNanos.merge(child.pid(), nanos, Math::max));
		});
		// A child that ended keeps its last CPU time; its pid may be reused by a new child.
		mChildNanos.keySet().removeIf(pid -> {
			if (alive.contains(pid)) {
				return false;
			}
			mEndedChildNanos += mChildNanos.get(pid);
			return true;
		});
		long children = mEndedChildNanos;
		for (final long nanos : mChildNanos.values()) {
			children += nanos;
		}
		return own + children;
	}
}
