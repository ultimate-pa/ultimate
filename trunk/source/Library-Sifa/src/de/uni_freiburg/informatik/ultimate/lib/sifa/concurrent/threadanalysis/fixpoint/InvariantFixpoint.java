/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.threadanalysis.fixpoint;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.publish.PublishOnAcquire;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.threadanalysis.ConcurrentSymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.threadanalysis.ThreadInvariants;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

final class InvariantFixpoint {
	enum StabilityOutcome {
		STABLE, ONE_EXTRA_ROUND, UPDATE
	}

	private static final int MUTEX_WIDENING_DELAY = 5;

	private final ConcurrentSymbolicTools mTools;
	private final IDomain mDomain;
	private final PublishOnAcquire mInitialMutexInvariants;
	private final int mWideningThreshold;
	private final Invariants mLocationInvariants;
	private PublishOnAcquire mMutexInvariants;
	private boolean mRerunWithStableInterferences;

	InvariantFixpoint(final ConcurrentSymbolicTools tools, final IDomain domain,
			final PublishOnAcquire initialMutexInvariants, final int wideningThreshold,
			final Set<IcfgLocation> joinedExitLocations) {
		mTools = tools;
		mDomain = domain;
		mInitialMutexInvariants = initialMutexInvariants;
		mWideningThreshold = wideningThreshold;
		mLocationInvariants = new Invariants(domain, joinedExitLocations);
		mMutexInvariants = initialMutexInvariants;
	}

	void resetStabilityCheck() {
		mRerunWithStableInterferences = false;
	}

	void configureForAnalysis(final ThreadInvariants invariants) {
		mLocationInvariants.rememberCurrentStates(invariants.locationInvariants());
		mTools.setPublication(mMutexInvariants);
	}

	StabilityOutcome checkInvariantStability(final ThreadInvariants invariants, final int iteration) {
		final PublishOnAcquire extracted = extractFrom(invariants);
		if (!extracted.isSubsumedBy(mMutexInvariants, mDomain)) {
			advance(extracted, iteration);
			return StabilityOutcome.UPDATE;
		}
		if (mRerunWithStableInterferences || mLocationInvariants.areUnchanged(invariants.locationInvariants())) {
			return StabilityOutcome.STABLE;
		}
		mRerunWithStableInterferences = true;
		mMutexInvariants = extracted;
		return StabilityOutcome.ONE_EXTRA_ROUND;
	}

	void advance(final ThreadInvariants invariants, final int iteration) {
		advance(extractFrom(invariants), iteration);
	}

	private PublishOnAcquire extractFrom(final ThreadInvariants invariants) {
		return mInitialMutexInvariants.recomputePublishedInvariants(invariants.locationInvariants(), mDomain,
				mTools::postWithoutInterference);
	}

	private void advance(final PublishOnAcquire extracted, final int iteration) {
		mRerunWithStableInterferences = false;
		mMutexInvariants = iteration >= mWideningThreshold + MUTEX_WIDENING_DELAY
				? mMutexInvariants.widen(extracted, mDomain)
				: extracted;
	}
}
