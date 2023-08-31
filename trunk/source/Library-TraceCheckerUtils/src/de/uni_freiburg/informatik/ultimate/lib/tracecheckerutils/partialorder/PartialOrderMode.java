/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

/**
 * Indicates a kind of partial order reduction.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public enum PartialOrderMode {
	/**
	 * No partial order reduction is performed.
	 */
	NONE(false, false, false, true),
	/**
	 * Sleep set partial order reduction. Delay sets are used to handle loops, and the reduced automaton is a
	 * sub-structure of the input.
	 */
	SLEEP_DELAY_SET(true, false, false, true),
	/**
	 * Sleep set partial order reduction. Unrolling and splitting is performed to achieve a minimal reduction (in terms
	 * of the language). This duplicates states of the input automaton.
	 */
	SLEEP_NEW_STATES(true, false, true, true),
	/**
	 * Persistent set reduction.
	 */
	PERSISTENT_SETS(false, true, false, false),
	/**
	 * Combines persistent set reduction with {@link SLEEP_DELAY_SET}.
	 */
	PERSISTENT_SLEEP_DELAY_SET(true, true, false, false),
	PERSISTENT_SLEEP_DELAY_SET_FIXEDORDER(true, true, false, true),
	/**
	 * Combines persistent set reduction with {@link SLEEP_NEW_STATES}.
	 */
	PERSISTENT_SLEEP_NEW_STATES(true, true, true, false),
	PERSISTENT_SLEEP_NEW_STATES_FIXEDORDER(true, true, true, true),
	/**
	 *
	 */
	DYNAMIC_ABSTRACTIONS(true, false, true, true);

	private final boolean mHasSleepSets;
	private final boolean mHasPersistentSets;
	private final boolean mDoesUnrolling;
	private final boolean mHasFixedOrder;

	PartialOrderMode(final boolean hasSleepSets, final boolean hasPersistentSets, final boolean doesUnrolling,
			final boolean hasFixedOrder) {
		mHasSleepSets = hasSleepSets;
		mHasPersistentSets = hasPersistentSets;
		mDoesUnrolling = doesUnrolling;
		mHasFixedOrder = hasFixedOrder;
	}

	public boolean hasSleepSets() {
		return mHasSleepSets;
	}

	public boolean hasPersistentSets() {
		return mHasPersistentSets;
	}

	public boolean doesUnrolling() {
		return mDoesUnrolling;
	}

	public boolean hasFixedOrder() {
		return mHasFixedOrder;
	}
}
