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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import java.io.Serializable;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;

/**
 * A Petri net transition.
 * 
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de) Copyright (C) 2011-2015 Matthias Heizmann
 *         (heizmann@informatik.uni-freiburg.de)
 * @param <S>
 *            symbol type
 * @param <C>
 *            place content type
 */
public class Transition<S, C> implements ITransition<S, C>, Serializable, Comparable<Transition<S, C>> {
	private static final long serialVersionUID = 5948089529814334197L;

	private final int mHashCode;
	private final S mSymbol;
	private final Collection<Place<C>> mPredecessors;
	private final Collection<Place<C>> mSuccessors;

	private final int mTotalOrderId;

	/**
	 * Constructor.
	 * <p>
	 * TODO Christian 2016-08-16: The code assumes that the Collection parameters are of type List. Why not explicitly
	 * type-check this?
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
	public Transition(final S symbol, final Collection<Place<C>> predecessors,
			final Collection<Place<C>> successors, final int totalOrderId) {
		mSymbol = symbol;
		mPredecessors = Collections.unmodifiableList((List<Place<C>>) predecessors);
		mSuccessors = Collections.unmodifiableList((List<Place<C>>) successors);
		mHashCode = computeHashCode();
		mTotalOrderId = totalOrderId;
	}

	@Override
	public S getSymbol() {
		return mSymbol;
	}

	@Override
	public Collection<Place<C>> getPredecessors() {
		return mPredecessors;
	}

	@Override
	public Collection<Place<C>> getSuccessors() {
		return mSuccessors;
	}

	@Override
	public int hashCode() {
		return mHashCode;
	}

	private int computeHashCode() {
		final int prime1 = 13;
		final int prime2 = 7;
		final int prime3 = 3;
		return prime1 * mPredecessors.hashCode() + prime2 * mSuccessors.hashCode() + prime3 * mSymbol.hashCode();
	}

	@Override
	public String toString() {
		return mSymbol.toString() + "[" + mTotalOrderId + "]";
	}

	public int getTotalOrderId() {
		return mTotalOrderId;
	}

	@Override
	public int compareTo(final Transition<S, C> other) {
		return mTotalOrderId - other.mTotalOrderId;
	}
}
