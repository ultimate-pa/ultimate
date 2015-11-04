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

package de.uni_freiburg.informatik.ultimate.core.services;

import de.uni_freiburg.informatik.ultimate.core.services.model.IProgressAwareTimer;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
final class ProgressAwareTimer implements IDeadlineProvider {

	private final IDeadlineProvider mParent;
	private final long mDeadline;

	private ProgressAwareTimer(final long deadline) {
		this(null, deadline);
	}

	private ProgressAwareTimer(final IDeadlineProvider parent, final long deadline) {
		assert deadline > 0;
		mParent = parent;
		mDeadline = deadline;
	}
	
	private boolean check() {
		return System.currentTimeMillis() > mDeadline;
	}

	@Override
	public boolean continueProcessing() {
		if (mParent == null) {
			return check();
		}
		return check() && mParent.continueProcessing();
	}

	@Override
	public IProgressAwareTimer getChildTimer(long timeout) {
		return createWithTimeout(this, timeout);
	}

	@Override
	public IProgressAwareTimer getChildTimer(double percentage) {
		return createWithPercentage(this, percentage);
	}

	@Override
	public long getDeadline() {
		return mDeadline;
	}

	static IDeadlineProvider createWithTimeout(final IDeadlineProvider parent, final long timeout) {
		return createWithDeadline(parent, System.currentTimeMillis() + timeout);
	}

	static IDeadlineProvider createWithDeadline(final IDeadlineProvider parent, final long deadline) {
		return new ProgressAwareTimer(parent, deadline);
	}

	static IDeadlineProvider createWithPercentage(final IDeadlineProvider parent, final double percentage) {
		assert parent != null;
		assert percentage > 0 && percentage <= 1.0;
		long current = System.currentTimeMillis();
		long currenttimeout = parent.getDeadline() - current;
		long newtimeout = (long) (currenttimeout * percentage);
		return createWithDeadline(parent, current + newtimeout);
	}
}
