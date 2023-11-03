/*
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.util;

import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.TerminationRequest;

public class TimeoutHandler implements TerminationRequest {

	TerminationRequest mStackedTermination;
	long mTimeoutStamp;
	boolean mTimeoutIsSet;

	public TimeoutHandler(final TerminationRequest stacked) {
		mStackedTermination = stacked;
		clearTimeout();
	}

	public void clearTimeout() {
		mTimeoutStamp = Long.MAX_VALUE;
		mTimeoutIsSet = false;
	}

	public void setTimeout(final long millis) {
		mTimeoutStamp = System.currentTimeMillis() + millis;
		mTimeoutIsSet = true;
	}

	public boolean timeoutIsSet() {
		return mTimeoutIsSet;
	}

	public long timeLeft() {
		if (!timeoutIsSet()) {
			return Long.MAX_VALUE;
		}
		return mTimeoutStamp - System.currentTimeMillis();
	}

	/**
	 * This returns null if there is no internal TerminationRequest.
	 */
	public TerminationRequest getTerminationRequest() {
		return mStackedTermination;
	}

	@Override
	public boolean isTerminationRequested() {
		if (mStackedTermination != null && mStackedTermination.isTerminationRequested()) {
			return true;
		}
		return System.currentTimeMillis() >= mTimeoutStamp;
	}
}
