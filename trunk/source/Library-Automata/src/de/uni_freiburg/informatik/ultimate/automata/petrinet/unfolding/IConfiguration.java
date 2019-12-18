/*
 * Copyright (C) 2019-2019 Mehdi Naouar
 * Copyright (C) 2009-2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;

/**
 * Interface for Configurations.
 *
 * @author Mehdi Naouar
 */
public interface IConfiguration<LETTER, PLACE> extends Set<Event<LETTER, PLACE>> {
	public List<Transition<LETTER, PLACE>> getPhi();
	
	/**
	 * Returns the causally minimal Events in this Configuration.
	 * An Event e is causally minimal in a Configuration,
	 * iff all Events preceding e are not in the configuration.
	 *
	 * @return causally minimal Events in this Configuration
	 */
	public IConfiguration<LETTER, PLACE> getMin();
	
	/**
	 * @return A new Configuration that contains the set difference between the original configuration and its minimum
	 *         regarding the casual relation.
	 */
	public IConfiguration<LETTER, PLACE> removeMin();

	public int compareTo(IConfiguration<LETTER, PLACE> c2);
}
