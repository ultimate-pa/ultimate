/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.datastructures.poset;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

/**
 * Lifts a lattice structure on the value type to a lattice structure on maps.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <K>
 *            the type of keys (unordered)
 * @param <V>
 *            the type of values (a lattice)
 */
public class CanonicalLatticeForMaps<K, V> extends CanonicalPartialComparatorForMaps<K, V>
		implements ILattice<Map<K, V>> {

	private final ILattice<V> mLattice;

	/**
	 * Creates a new map lattice.
	 *
	 * @param lattice
	 *            The underlying value lattice
	 */
	public CanonicalLatticeForMaps(final ILattice<V> lattice) {
		super(lattice);
		mLattice = lattice;
	}

	@Override
	public Map<K, V> getBottom() {
		return Collections.emptyMap();
	}

	@Override
	public Map<K, V> getTop() {
		throw new UnsupportedOperationException("Map lattice has no top element unless key domain is finite");
	}

	@Override
	public Map<K, V> supremum(final Map<K, V> h1, final Map<K, V> h2) {
		final Map<K, V> result = new HashMap<>();

		for (final Map.Entry<K, V> entry : h1.entrySet()) {
			final V value;
			if (h2.containsKey(entry.getKey())) {
				value = mLattice.supremum(entry.getValue(), h2.get(entry.getKey()));
			} else {
				value = entry.getValue();
			}
			result.put(entry.getKey(), value);
		}

		for (final Map.Entry<K, V> entry : h2.entrySet()) {
			if (!result.containsKey(entry.getKey())) {
				result.put(entry.getKey(), entry.getValue());
			}
		}

		return result;
	}

	@Override
	public Map<K, V> infimum(final Map<K, V> h1, final Map<K, V> h2) {
		final Map<K, V> smaller;
		final Map<K, V> bigger;
		if (h1.size() < h2.size()) {
			smaller = h1;
			bigger = h2;
		} else {
			smaller = h2;
			bigger = h1;
		}

		final Map<K, V> result = new HashMap<>();
		for (final Map.Entry<K, V> entry : smaller.entrySet()) {
			if (bigger.containsKey(entry.getKey())) {
				final V value = mLattice.infimum(entry.getValue(), bigger.get(entry.getKey()));
				result.put(entry.getKey(), value);
			}
		}

		return result;
	}
}
