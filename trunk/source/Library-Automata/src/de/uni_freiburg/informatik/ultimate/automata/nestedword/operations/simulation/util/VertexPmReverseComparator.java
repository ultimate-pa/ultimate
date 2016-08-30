/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2009-2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util;

import java.util.Comparator;

/**
 * Compares two vertices based on their progress measure as returned by
 * {@link Vertex#getPM(java.util.Set, int)} but with reverse ordering, i.e.
 * greater values come before smaller ones.
 * 
 * @author Daniel Tischner
 *
 * @param <LETTER>
 *            Letter class for vertices
 * @param <STATE>
 *            State class for vertices
 */
public final class VertexPmReverseComparator<LETTER, STATE> implements Comparator<Vertex<LETTER, STATE>> {

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Comparator#compare(java.lang.Object, java.lang.Object)
	 */
	@Override
	public int compare(final Vertex<LETTER, STATE> firstVertex, final Vertex<LETTER, STATE> secondVertex) {
		return Integer.compare(secondVertex.getPM(null, 0), firstVertex.getPM(null, 0));
	}

}
