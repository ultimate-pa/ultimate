/*
 * Copyright (C) 2016-2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.util;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * General data structure interface to represent sets of pairs, i.e., binary relations.
 * <p>
 * The interface abstracts from the data structure that is used in the background, but also allows to return the data
 * structure for efficient use.
 * <p>
 * Note: Two calls to the {@link #iterator()} method may result in different {@link Pair} objects.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <E>
 *            element type
 * @param <T>
 *            data structure type
 */
public interface ISetOfPairs<E, T> extends Iterable<Pair<E, E>> {
	/**
	 * @param lhs
	 *            Left-hand side entry.
	 * @param rhs
	 *            right-hand side entry
	 */
	void addPair(E lhs, E rhs);

	/**
	 * @param lhs
	 *            Lhs element.
	 * @param rhs
	 *            rhs element
	 * @return {@code true} iff the pair (lhs, rhs) is contained in the set of pairs.
	 */
	boolean containsPair(E lhs, E rhs);

	/**
	 * @return The data structure implementing the relation.
	 */
	T getRelation();
}
