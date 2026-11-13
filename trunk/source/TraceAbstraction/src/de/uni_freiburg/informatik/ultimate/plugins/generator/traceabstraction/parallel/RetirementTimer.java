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
 * A timer that also expires when its worker is retired. Everything the worker runs polls {@link #continueProcessing()}
 * through the progress monitor of its services, so a retirement stops a running solver query, automaton operation or
 * search the way a timeout does. The {@link HeapWatchdog} retires workers when the heap fills up. Once retired, the
 * timer stays expired. The worker tells the timer when it {@link #stopped()}, so that the watchdog knows when the
 * memory of a retired worker is free.
 *
 * @author Max Barth (Max.Barth@lmu.de)
 */
public final class RetirementTimer implements IProgressAwareTimer {

	private final IProgressAwareTimer mTimer;
	// Timers created from this one report to the same root, so the caller only has to retire the timer it created.
	private final RetirementTimer mRoot;
	private volatile String mReason;
	private volatile boolean mStopped;

	public RetirementTimer(final IProgressAwareTimer timer) {
		this(timer, null);
	}

	private RetirementTimer(final IProgressAwareTimer timer, final RetirementTimer root) {
		mTimer = timer;
		mRoot = root == null ? this : root;
	}

	/**
	 * Expires this timer and every timer created from it.
	 *
	 * @param reason
	 *            why the worker retires, for the log
	 */
	public void retire(final String reason) {
		mRoot.mReason = reason;
	}

	/**
	 * @return whether the worker of this timer was retired
	 */
	public boolean isRetired() {
		return mRoot.mReason != null;
	}

	/**
	 * @return why the worker was retired, or null if it was not
	 */
	public String getReason() {
		return mRoot.mReason;
	}

	/**
	 * Called by the worker when it leaves its {@code run()}, retired or not.
	 */
	public void stopped() {
		mRoot.mStopped = true;
	}

	/**
	 * @return whether the worker of this timer left its {@code run()}
	 */
	public boolean hasStopped() {
		return mRoot.mStopped;
	}

	@Override
	public boolean continueProcessing() {
		return !isRetired() && mTimer.continueProcessing();
	}

	@Override
	public IProgressAwareTimer getChildTimer(final long timeout) {
		return new RetirementTimer(mTimer.getChildTimer(timeout), mRoot);
	}

	@Override
	public IProgressAwareTimer getChildTimer(final double percentage) {
		return new RetirementTimer(mTimer.getChildTimer(percentage), mRoot);
	}

	@Override
	public IProgressAwareTimer getTimer(final long timeout) {
		return new RetirementTimer(mTimer.getTimer(timeout), mRoot);
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
