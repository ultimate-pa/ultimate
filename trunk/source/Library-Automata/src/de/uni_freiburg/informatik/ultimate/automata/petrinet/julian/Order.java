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

import java.util.Comparator;

/**
 * Order of events.
 * 
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <S>
 *            symbol type
 * @param <C>
 *            place content type
 */
public abstract class Order<S, C> implements Comparator<Event<S, C>> {
	@SuppressWarnings("squid:S1698")
	@Override
	public int compare(final Event<S, C> o1, final Event<S, C> o2) {
		// equality intended here
		if (o1 == o2) {
			// mLogger.info("compared " + o1 + " with itself.");
			return 0;
		}
		final Configuration<S, C> c1 = o1.getLocalConfiguration();
		final Configuration<S, C> c2 = o2.getLocalConfiguration();
		assert !(c1.containsAll(c2) && c2.containsAll(c1)) : "Different events with equal local configurations. equals:"
				+ c1.equals(c2);
		return compare(c1, c2);
	}

	/**
	 * Compares two configurations.
	 * 
	 * @param o1
	 *            first configuration
	 * @param o2
	 *            second configuration
	 * @return the value according to the {@link Comparator} interface
	 */
	public abstract int compare(Configuration<S, C> o1, Configuration<S, C> o2);
}
