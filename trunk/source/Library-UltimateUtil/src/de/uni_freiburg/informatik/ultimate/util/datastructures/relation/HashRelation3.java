/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.util.datastructures.relation;

import java.util.Collections;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

/**
 * Ternary relation implemented via nested HashMaps.
 * @author Matthias Heizmann
 *
 */
public class HashRelation3<K1, K2, K3> implements Iterable<Triple<K1, K2, K3>> {
	private final NestedMap3<K1, K2, K3, IsContained> mBackingMap = new NestedMap3<>();

	public boolean addTriple(final K1 fst, final K2 snd, final K3 trd) {
		final IsContained isContained = mBackingMap.put(fst, snd, trd, IsContained.IsContained);
		return isContained == IsContained.IsContained;
	}

	public Set<K1> projectToFst() {
		return mBackingMap.keySet();
	}

	public Set<K2> projectToSnd(final K1 k1) {
		 final NestedMap2<K2, K3, IsContained> snd2trd2ic = mBackingMap.get(k1);
		 if (snd2trd2ic == null) {
			 return Collections.emptySet();
		 } else {
			 return snd2trd2ic.keySet();
		 }
	}

	public Set<K3> projectToTrd(final K1 k1, final K2 k2) {
		 final Map<K3, IsContained> trd2ic  = mBackingMap.get(k1, k2);
		 if (trd2ic == null) {
			 return Collections.emptySet();
		 } else {
			 return trd2ic.keySet();
		 }
	}

	@Override
	public Iterator<Triple<K1, K2, K3>> iterator() {
		return new Iterator<Triple<K1, K2, K3>>() {

			Iterator<Quad<K1, K2, K3, IsContained>> mBackingMapIterator = mBackingMap.entrySet().iterator();
			private Triple<K1, K2, K3> mNext;

			@Override
			public boolean hasNext() {
				if (mNext != null) {
					return true;
				}
				findNext();
				return mNext != null;
			}

			private void findNext() {
				if (mNext != null) {
					// nothing to do
					return;
				}
				Quad<K1, K2, K3, IsContained> next = null;
				while (mBackingMapIterator.hasNext()) {
					final Quad<K1, K2, K3, IsContained> current = mBackingMapIterator.next();
					if (current.getFourth() != null) {
						next = current;
						break;
					}
				}
				if (next != null) {
					assert next.getFourth() != null;
					mNext = new Triple<>(next.getFirst(), next.getSecond(), next.getThird());
				} else {
					mNext = null;
				}
			}

			@Override
			public Triple<K1, K2, K3> next() {
				findNext();
				if (mNext == null) {
					throw new UnsupportedOperationException("check hasNext first");
				}
				final Triple<K1, K2, K3> next = mNext;
				mNext = null;
				return next;
			}
		};
	}


}
