/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.coreplugin.services;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Objects;
import java.util.concurrent.CountDownLatch;

import de.uni_freiburg.informatik.ultimate.core.model.IToolchainProgressMonitor;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IStorable;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainCancel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ProgressMonitorService implements IStorable, IProgressMonitorService, IProgressAwareTimer {

	private static final String STORAGE_KEY = "CancelNotificationService";

	private final IToolchainProgressMonitor mMonitor;
	private final ILogger mLogger;
	private final IToolchainCancel mToolchainCancel;

	private final Deque<IProgressAwareTimer> mTimers;
	private IProgressAwareTimer mActiveTimer;
	private IProgressAwareTimer mRootTimer;
	private boolean mCancelRequest;

	public ProgressMonitorService(final IToolchainProgressMonitor monitor, final ILogger logger,
			final IToolchainCancel cancel) {
		mMonitor = Objects.requireNonNull(monitor, "monitor may not be null");
		mLogger = Objects.requireNonNull(logger, "logger may not be null");
		mToolchainCancel = Objects.requireNonNull(cancel, "cancel may not be null");
		mCancelRequest = false;
		mTimers = new ArrayDeque<>();
	}

	@Override
	public boolean continueProcessing() {
		final boolean cancel =
				mMonitor.isCanceled() || mCancelRequest || (mActiveTimer != null && !mActiveTimer.continueProcessing());
		if (cancel && mLogger.isDebugEnabled()) {
			mLogger.debug("Do not continue processing!");
		}
		return !cancel;
	}

	@Override
	public boolean continueProcessingRoot() {
		final boolean cancel =
				mMonitor.isCanceled() || mCancelRequest || (mRootTimer != null && !mRootTimer.continueProcessing());
		if (cancel && mLogger.isDebugEnabled()) {
			mLogger.debug("Do not continue processing!");
		}
		return !cancel;
	}

	@Override
	public void setSubtask(final String task) {
		mMonitor.subTask(task);
	}

	@Override
	public void setDeadline(final long deadline) {
		if (System.currentTimeMillis() >= deadline) {
			mLogger.warn(
					String.format("Deadline was set to a date in the past, " + "effectively stopping the toolchain. "
							+ "Is this what you intended? Value of date was %,d", deadline));

		}
		if (mActiveTimer != null) {
			mLogger.warn("Replacing old deadline");
		}
		mTimers.clear();
		mActiveTimer = null;
		mRootTimer = ProgressAwareTimer.createWithDeadline(null, deadline);
		addChildTimer(mRootTimer);
	}

	static ProgressMonitorService getService(final IToolchainStorage storage) {
		assert storage != null;
		return (ProgressMonitorService) storage.getStorable(STORAGE_KEY);
	}

	public static String getServiceKey() {
		return STORAGE_KEY;
	}

	@Override
	public void destroy() {
		mMonitor.done();
	}

	@Override
	public CountDownLatch cancelToolchain() {
		mCancelRequest = true;
		return mToolchainCancel.cancelToolchain();
	}

	@Override
	public IProgressAwareTimer getTimer(final long timeout) {
		return ProgressAwareTimer.createWithTimeout(null, timeout);
	}

	@Override
	public IProgressAwareTimer getChildTimer(final long timeout) {
		return ProgressAwareTimer.createWithTimeout(this, timeout);
	}

	@Override
	public IProgressAwareTimer getChildTimer(final double percentage) {
		return ProgressAwareTimer.createWithPercentage(this, percentage);
	}

	@Override
	public long getDeadline() {
		if (mActiveTimer == null) {
			return ProgressAwareTimer.createWithDeadline(null, Long.MAX_VALUE).getDeadline();
		}
		return mActiveTimer.getDeadline();
	}

	@Override
	public IProgressAwareTimer getParent() {
		if (mActiveTimer == null) {
			return null;
		}
		return mActiveTimer.getParent();
	}

	@Override
	public void addChildTimer(final IProgressAwareTimer timer) {
		if (timer == null) {
			throw new IllegalArgumentException("Cannot add null timer");
		}
		if (checkParents(timer)) {
			throw new IllegalArgumentException(
					"This timer would create a timer cycle, because itself, its parent or its grandparents are this object");
		}
		mTimers.push(timer);
		mActiveTimer = timer;
	}

	/**
	 * @return true if the timer or one of its parents are this, thus creating a timer cycle
	 */
	private boolean checkParents(final IProgressAwareTimer timer) {
		IProgressAwareTimer current = timer;
		while (current != null) {
			if (current == this) {
				return true;
			}
			current = current.getParent();
		}
		return false;
	}

	@Override
	public IProgressAwareTimer removeChildTimer() {
		if (mTimers.isEmpty()) {
			assert mActiveTimer == null;
			return null;
		}
		final IProgressAwareTimer activeTimer = mTimers.pop();
		assert mActiveTimer == activeTimer;
		if (mTimers.isEmpty()) {
			mActiveTimer = null;
		} else {
			mActiveTimer = mTimers.peek();
		}
		return activeTimer;
	}

}
