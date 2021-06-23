/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
final class ProgressAwareTimer implements IProgressAwareTimer {

	private final IProgressAwareTimer mParent;
	private final long mDeadline;

	private ProgressAwareTimer(final IProgressAwareTimer parent, final long deadline) {
		if (deadline <= 0 && deadline != -1) {
			throw new IllegalArgumentException("deadline must be positive or -1");
		}
		mParent = parent;
		mDeadline = deadline;
	}

	private boolean isTimeout() {
		if (mDeadline == -1) {
			return false;
		}
		return System.currentTimeMillis() > mDeadline;
	}

	@Override
	public boolean continueProcessing() {
		if (mParent == null) {
			return !isTimeout();
		}
		return !isTimeout() && mParent.continueProcessing();
	}

	@Override
	public IProgressAwareTimer getTimer(final long timeout) {
		return createWithTimeout(null, timeout);
	}

	@Override
	public IProgressAwareTimer getChildTimer(final long timeout) {
		return createWithTimeout(this, timeout);
	}

	@Override
	public IProgressAwareTimer getChildTimer(final double percentage) {
		return createWithPercentage(this, percentage);
	}

	@Override
	public long getDeadline() {
		return mDeadline;
	}

	static IProgressAwareTimer createWithTimeout(final IProgressAwareTimer parent, final long timeout) {
		return createWithDeadline(parent, System.currentTimeMillis() + timeout);
	}

	static IProgressAwareTimer createWithDeadline(final IProgressAwareTimer parent, final long deadline) {
		return new ProgressAwareTimer(parent, deadline);
	}

	static IProgressAwareTimer createWithPercentage(final IProgressAwareTimer parent, final double percentage) {
		if (parent == null) {
			throw new IllegalArgumentException("parent may not be null");
		}
		if (percentage <= 0 || percentage > 1.0) {
			throw new IllegalArgumentException(
					"percentage must be larger than zero and smaller or equal to one, but was " + percentage);
		}
		if (parent.getDeadline() == -1) {
			return createWithDeadline(parent, -1);
		}
		final long current = System.currentTimeMillis();
		final long currenttimeout = parent.getDeadline() - current;
		final long newtimeout = (long) (currenttimeout * percentage);
		return createWithDeadline(parent, current + newtimeout);
	}

	@Override
	public IProgressAwareTimer getParent() {
		return mParent;
	}

	@Override
	public long remainingTime() {
		if (mDeadline == -1) {
			if (mParent != null) {
				return mParent.remainingTime();
			}
			return -1;
		}
		final long current = System.currentTimeMillis();

		final long remainingTime = Math.min(0, mDeadline - current);
		final long parentRemainingTime = mParent == null ? -1 : mParent.remainingTime();
		if (parentRemainingTime == -1) {
			return remainingTime;
		}
		return Math.min(remainingTime, parentRemainingTime);
	}
}
