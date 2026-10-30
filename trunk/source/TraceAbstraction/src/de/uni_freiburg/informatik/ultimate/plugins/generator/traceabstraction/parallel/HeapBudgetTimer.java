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

import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;

/**
 * A timer that also expires when the JVM uses more heap than a budget allows. It bounds a worker in memory the way
 * the wrapped timer bounds it in time: everything that polls {@link #continueProcessing()} stops once either budget is
 * exceeded.
 * <p>
 * By default the used heap of the whole JVM counts, garbage included, so the heap of other workers counts as well.
 * That is intended for a worker that allocates faster than the collector frees: it makes the JVM grow its heap, which
 * it does not return, and that is what exceeds the memory limit of the process.
 * <p>
 * With {@code confirmWithGc}, as the k-induction worker uses it, only the live heap counts for stopping: a used or
 * committed heap above the budget triggers a full garbage collection, and the budget is exceeded only if the used heap
 * is still above it afterwards. Other workers churn through gigabytes of garbage while k-induction runs, and that must
 * not stop it. The committed heap counts as a trigger because it is what the process pays for: G1 answers a high
 * allocation rate by growing its heap, also when little of it is live, and returns memory only after a full
 * collection. So the collection also trims a heap that churn made grow, which keeps the process below its memory limit
 * without stopping anything. If the heap stays committed above the budget after a collection (G1 keeps a part of it
 * free), the committed heap triggers the next collection only once it has grown by another tenth of the maximum heap;
 * otherwise every poll would collect again. To bound the cost of the collections, there is at most one every
 * {@link #MIN_GC_INTERVAL_NANOS}; in between, the budget is not checked. Once exceeded, such a timer stays expired.
 *
 * @author Max Barth (Max.Barth@lmu.de)
 */
public final class HeapBudgetTimer implements IProgressAwareTimer {

	private static final long MIN_GC_INTERVAL_NANOS = 5_000_000_000L;

	private final IProgressAwareTimer mTimer;
	private final long mBudgetBytes;
	private final boolean mConfirmWithGc;
	// Timers created from this one report to the same root, so the caller only has to ask the timer it created.
	private final HeapBudgetTimer mRoot;
	private volatile long mHeapUsedWhenExceeded = -1;
	// When the root last collected garbage to confirm an exceeded budget; only used with mConfirmWithGc
	private volatile long mLastGcNanos;
	private volatile boolean mCollectedBefore;
	private volatile int mCollections;
	// The committed heap above which the root collects; only used with mConfirmWithGc
	private volatile long mCommittedTrigger;

	public HeapBudgetTimer(final IProgressAwareTimer timer, final long budgetBytes) {
		this(timer, budgetBytes, false);
	}

	/**
	 * @param confirmWithGc
	 *            whether only the live heap counts, see the class documentation
	 */
	public HeapBudgetTimer(final IProgressAwareTimer timer, final long budgetBytes, final boolean confirmWithGc) {
		this(timer, budgetBytes, confirmWithGc, null);
	}

	private HeapBudgetTimer(final IProgressAwareTimer timer, final long budgetBytes, final boolean confirmWithGc,
			final HeapBudgetTimer root) {
		if (budgetBytes <= 0) {
			throw new IllegalArgumentException("The heap budget must be positive, but is " + budgetBytes);
		}
		mTimer = timer;
		mBudgetBytes = budgetBytes;
		mConfirmWithGc = confirmWithGc;
		mRoot = root == null ? this : root;
		mCommittedTrigger = budgetBytes;
	}

	@Override
	public boolean continueProcessing() {
		if (!mTimer.continueProcessing()) {
			return false;
		}
		if (mConfirmWithGc && isHeapBudgetExceeded()) {
			return false;
		}
		final long used = usedHeap();
		if (!mConfirmWithGc) {
			if (used <= mBudgetBytes) {
				return true;
			}
			mRoot.mHeapUsedWhenExceeded = used;
			return false;
		}
		if (used <= mBudgetBytes && Runtime.getRuntime().totalMemory() <= mRoot.mCommittedTrigger) {
			return true;
		}
		return mRoot.confirmExceeded();
	}

	/**
	 * Collects garbage unless that was done recently, which also lets the JVM shrink its heap, and records the budget as
	 * exceeded if the live heap is still above it.
	 *
	 * @return whether processing may continue
	 */
	private synchronized boolean confirmExceeded() {
		if (mHeapUsedWhenExceeded >= 0) {
			return false;
		}
		final long now = System.nanoTime();
		if (mCollectedBefore && now - mLastGcNanos < MIN_GC_INTERVAL_NANOS) {
			return true;
		}
		System.gc();
		mCollections++;
		mCollectedBefore = true;
		mLastGcNanos = System.nanoTime();
		final long live = usedHeap();
		final Runtime runtime = Runtime.getRuntime();
		mCommittedTrigger = Math.max(mBudgetBytes, runtime.totalMemory() + runtime.maxMemory() / 10);
		if (live > mBudgetBytes) {
			mHeapUsedWhenExceeded = live;
			return false;
		}
		return true;
	}

	private static long usedHeap() {
		final Runtime runtime = Runtime.getRuntime();
		return runtime.totalMemory() - runtime.freeMemory();
	}

	/**
	 * @return whether this timer, or one created from it, expired because of the heap budget
	 */
	public boolean isHeapBudgetExceeded() {
		return mRoot.mHeapUsedWhenExceeded >= 0;
	}

	/**
	 * @return the used heap in bytes that exceeded the budget (after the garbage collection if the budget is confirmed
	 *         with one), or -1 if the budget was not exceeded
	 */
	public long getHeapUsedWhenExceeded() {
		return mRoot.mHeapUsedWhenExceeded;
	}

	/**
	 * @return how many garbage collections this timer, or one created from it, has run to check the budget
	 */
	public int getCollections() {
		return mRoot.mCollections;
	}

	/**
	 * @return the budget in bytes
	 */
	public long getBudgetBytes() {
		return mBudgetBytes;
	}

	@Override
	public IProgressAwareTimer getChildTimer(final long timeout) {
		return new HeapBudgetTimer(mTimer.getChildTimer(timeout), mBudgetBytes, mConfirmWithGc, mRoot);
	}

	@Override
	public IProgressAwareTimer getChildTimer(final double percentage) {
		return new HeapBudgetTimer(mTimer.getChildTimer(percentage), mBudgetBytes, mConfirmWithGc, mRoot);
	}

	@Override
	public IProgressAwareTimer getTimer(final long timeout) {
		return new HeapBudgetTimer(mTimer.getTimer(timeout), mBudgetBytes, mConfirmWithGc, mRoot);
	}

	@Override
	public IProgressAwareTimer getParent() {
		return mTimer.getParent();
	}

	@Override
	public long getDeadline() {
		return mTimer.getDeadline();
	}

	@Override
	public long remainingTime() {
		return mTimer.remainingTime();
	}
}
