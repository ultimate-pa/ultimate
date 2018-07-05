/*
 * Copyright (C) 2012-2015 Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;

/**
 * An inhibitor transition.
 * 
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <S>
 *            symbol type
 * @param <C>
 *            place content type
 */
public class InhibitorTransition<S, C> extends Transition<S, C> {
	private static final long serialVersionUID = 933451776613619705L;

	private final Collection<Place<C>> mInhibitors;

	/**
	 * Constructor.
	 * 
	 * @param symbol
	 *            symbol
	 * @param predecessors
	 *            predecessor places
	 * @param inhibitors
	 *            inhibitor places
	 * @param successors
	 *            successor places
	 * @param totalOrderId
	 *            total order ID
	 */
	public InhibitorTransition(final S symbol, final Collection<Place<C>> predecessors,
			final Collection<Place<C>> inhibitors, final Collection<Place<C>> successors,
			final int totalOrderId) {
		super(symbol, predecessors, successors, totalOrderId);
		mInhibitors = inhibitors;
	}

	public Collection<Place<C>> getInhibitors() {
		return mInhibitors;
	}
}
