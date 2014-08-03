/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
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

public abstract class Order<S, C> implements Comparator<Event<S, C>> {
	@Override
	public int compare(Event<S, C> o1, Event<S, C> o2) {
		if (o1 == o2) {
			//s_Logger.info("compared " + o1 + " with itsself.");
			return 0;
		}
		Configuration<S, C> c1 = o1.getLocalConfiguration();
		Configuration<S, C> c2 = o2.getLocalConfiguration();
		assert !(c1.containsAll(c2) && c2.containsAll(c1)) : "Different events with equal local configurations. equals:"
				+ c1.equals(c2);
		int result = compare(c1, c2);

		return result;
	}

	public abstract int compare(Configuration<S, C> o1, Configuration<S, C> o2);
}
