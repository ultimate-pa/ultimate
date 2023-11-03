/*
 * Copyright (C) 2011-2015 Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures;

import java.io.Serializable;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.util.HashUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * A Petri net transition.
 *
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de) Copyright (C) 2011-2015 Matthias Heizmann
 *         (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            symbol type
 * @param <PLACE>
 *            place content type
 */
public class Transition<LETTER, PLACE> implements Serializable, Comparable<Transition<LETTER, PLACE>> {
	private static final long serialVersionUID = 5948089529814334197L;

	// See https://github.com/ultimate-pa/ultimate/pull/595 for discussion
	private static final boolean USE_HASH_JENKINS = false;

	private final int mHashCode;
	private final LETTER mSymbol;
	private final ImmutableSet<PLACE> mPredecessors;
	private final ImmutableSet<PLACE> mSuccessors;

	private final int mTotalOrderId;

	/**
	 * Constructor.
	 *
	 * @param symbol
	 *            symbol
	 * @param predecessors
	 *            predecessor places
	 * @param successors
	 *            successor places
	 * @param totalOrderId
	 *            total order ID
	 */
	public Transition(final LETTER symbol, final ImmutableSet<PLACE> predecessors, final ImmutableSet<PLACE> successors,
			final int totalOrderId) {
		mSymbol = Objects.requireNonNull(symbol, "Transition must not be labeled with null");
		mPredecessors = predecessors;
		mSuccessors = successors;
		mTotalOrderId = totalOrderId;

		if (USE_HASH_JENKINS) {
			// The totalOrderId should not be used verbatim as hash code,
			// because this would cause frequent hash collisions for e.g. sets or lists of transitions.
			mHashCode = HashUtils.hashJenkins(29, mTotalOrderId);
		} else {
			mHashCode = mTotalOrderId;
		}
	}

	public LETTER getSymbol() {
		return mSymbol;
	}

	public ImmutableSet<PLACE> getPredecessors() {
		return mPredecessors;
	}

	public ImmutableSet<PLACE> getSuccessors() {
		return mSuccessors;
	}

	@Override
	public int hashCode() {
		return mHashCode;
	}

	@Override
	public boolean equals(final Object obj) {
		// Transitions are unified by the TransitionUnifier class, hence reference equality suffices here.
		return this == obj;
	}

	@Override
	public String toString() {
		return mSymbol.toString() + "[" + mTotalOrderId + "]";
	}

	public int getTotalOrderId() {
		return mTotalOrderId;
	}

	@Override
	public int compareTo(final Transition<LETTER, PLACE> other) {
		return mTotalOrderId - other.mTotalOrderId;
	}
}
