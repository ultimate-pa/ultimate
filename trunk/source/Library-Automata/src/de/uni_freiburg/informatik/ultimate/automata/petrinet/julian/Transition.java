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

public class Transition<S, C> implements ITransition<S, C>, Serializable,
		Comparable<Transition<S, C>> {
	private static final long serialVersionUID = 5948089529814334197L;

	private final int mHashCode;
	private final S mSymbol;
	private final Collection<Place<S, C>> mPredecessors;
	private final Collection<Place<S, C>> mSuccessors;

	private final int mTotalOrderID;

	public Transition(S symbol, Collection<Place<S, C>> predecessors,
			Collection<Place<S, C>> successors, int totalOrderID) {
		mSymbol = symbol;
		mPredecessors = Collections
				.unmodifiableList((List<Place<S, C>>) predecessors);
		mSuccessors = Collections
				.unmodifiableList((List<Place<S, C>>) successors);
		mHashCode = computeHashCode();
		mTotalOrderID = totalOrderID;
	}

	@Override
	public S getSymbol() {
		return mSymbol;
	}

	@Override
	public Collection<Place<S, C>> getPredecessors() {
		return mPredecessors;
	}

	@Override
	public Collection<Place<S, C>> getSuccessors() {
		return mSuccessors;
	}

	@Override
	public int hashCode() {
		return mHashCode;
	}

	public int computeHashCode() {
		return 13 * mPredecessors.hashCode() + 7 * mSuccessors.hashCode() + 3
				* mSymbol.hashCode();
	}

	@Override
	public String toString() {
		return mSymbol.toString()+"["+mTotalOrderID+"]";
	}

	public int getTotalOrderID() {
		return mTotalOrderID;
	}

	@Override
	public int compareTo(Transition<S, C> o) {
		return mTotalOrderID - o.mTotalOrderID;
	}

}
