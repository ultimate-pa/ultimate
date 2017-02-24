/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

/**
 * Partition implementation of a set of pairs together with a map for efficient {@link #containsPair(Object, Object)}
 * checks.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <E>
 *            element type
 */
public class PartitionAndMapBackedSetOfPairs<E> extends PartitionBackedSetOfPairs<E> {
	private final Map<E, Set<E>> mElem2block;

	/**
	 * @param partition
	 *            Partition.
	 */
	public PartitionAndMapBackedSetOfPairs(final Collection<Set<E>> partition) {
		super(partition);
		mElem2block = new HashMap<>();
		for (final Set<E> block : mPartition) {
			for (final E elem : block) {
				mElem2block.put(elem, block);
			}
		}
	}

	@Override
	public boolean containsPair(final E lhs, final E rhs) {
		return mElem2block.get(lhs).contains(rhs);
	}

	public Map<E, Set<E>> getMap() {
		return mElem2block;
	}
}
