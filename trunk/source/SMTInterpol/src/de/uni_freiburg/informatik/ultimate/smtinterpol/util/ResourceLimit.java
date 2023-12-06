/*
 * Copyright (C) 2023 Damien Zufferey
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.	See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.	If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.util;

import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.TerminationRequest;

public class ResourceLimit implements TerminationRequest {

	TerminationRequest mStackedTermination;
	long mResourceLimit;
	boolean mResourceLimitIsSet;

	public ResourceLimit(final TerminationRequest stacked) {
		mStackedTermination = stacked;
		clearResourceLimit();
	}

	public void clearResourceLimit() {
		mResourceLimit= Long.MAX_VALUE;
		mResourceLimitIsSet = false;
	}

	public void setResourceLimit(final long limit) {
		if (limit > 0) {
			mResourceLimit = limit;
			mResourceLimitIsSet = true;
		} else {
			clearResourceLimit();
		}
	}

	public boolean resourceLimitIsSet() {
		return mResourceLimitIsSet;
	}

	public long resourceLeft() {
		return mResourceLimit;
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
		} else if (mResourceLimitIsSet) {
			mResourceLimit -= 1;
			return mResourceLimit <= 0;
		} else {
			return false;
		}
	}
}
