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

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.publish.PublishOnAcquire;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.threadanalysis.ConcurrentSymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

final class MutexInvariantFixpoint {
	private static final int WIDENING_DELAY = 5;

	private final ConcurrentSymbolicTools mTools;
	private final IDomain mDomain;
	private final PublishOnAcquire mInitial;
	private final int mWideningThreshold;
	private PublishOnAcquire mCurrent;
	private PublishOnAcquire mExtracted;

	MutexInvariantFixpoint(final ConcurrentSymbolicTools tools, final IDomain domain,
			final PublishOnAcquire initial, final int wideningThreshold) {
		mTools = tools;
		mDomain = domain;
		mInitial = initial;
		mWideningThreshold = wideningThreshold;
		mCurrent = initial;
	}

	void configureForAnalysis() {
		mTools.setPublication(mCurrent);
	}

	void extractFrom(final Map<IcfgLocation, IPredicate> locationPredicates) {
		mExtracted = mInitial.recomputePublishedInvariants(locationPredicates, mDomain, mTools::postWithoutInterference);
	}

	boolean isStable() {
		return mExtracted.isSubsumedBy(mCurrent, mDomain);
	}

	void acceptExtracted() {
		mCurrent = mExtracted;
	}

	void advance(final int iteration) {
		mCurrent = iteration >= mWideningThreshold + WIDENING_DELAY ? mCurrent.widen(mExtracted, mDomain) : mExtracted;
	}
}
