/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core;

import java.util.concurrent.atomic.AtomicInteger;

/**
 * Search statistics.
 */
public class SearchStats {
	private int mFailedSteps;
	private int mSuccessfulSteps;
	private int mCanceledSpeculativeSteps;
	private final AtomicInteger mSkippedDuplicateMinimizerSteps = new AtomicInteger();
	private final AtomicInteger mOverallTestCount = new AtomicInteger();
	private final AtomicInteger mChangeConflicts = new AtomicInteger();
	
	public int getCanceledSpeculativeSteps() {
		return mCanceledSpeculativeSteps;
	}
	
	public AtomicInteger getChangeConflicts() {
		return mChangeConflicts;
	}
	
	public int getFailedSteps() {
		return mFailedSteps;
	}
	
	public AtomicInteger getOverallTestCount() {
		return mOverallTestCount;
	}
	
	public AtomicInteger getSkippedDuplicateMinimizerSteps() {
		return mSkippedDuplicateMinimizerSteps;
	}
	
	public int getSuccessfulSteps() {
		return mSuccessfulSteps;
	}
	
	/**
	 * Increments the number of successful steps.
	 */
	public void incrementSuccessfulSteps() {
		++mSuccessfulSteps;
	}
	
	/**
	 * Increments the number of failed steps.
	 */
	public void incrementFailedSteps() {
		++mFailedSteps;
	}
	
	/**
	 * @param count
	 *            Number to add to canceled speculative steps.
	 */
	public void addToCanceledSpeculativeSteps(final int count) {
		mCanceledSpeculativeSteps += count;
	}
}
