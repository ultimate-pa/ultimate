/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <T>
 * @param <U>
 */
public class BinaryRelation<T, U> {

	private final Map<T, Set<U>> mBacking = new HashMap<T, Set<U>>();

	public BinaryRelation() {
		// default constructor necessary because there is another one
	}

	/**
	 * Constructs a binary relation from a map (the binary relation will be "rechtseindeutig").
	 * Note that, as it is implemented now, this map will be unmodifiable (because we use Collections.singleton),
	 *  i.e. addPair calls will crash.
	 *
	 * @param map
	 */
	public BinaryRelation(Map<T, U> map) {
		for (Entry<T, U> en : map.entrySet()) {
			mBacking.put(en.getKey(), Collections.singleton(en.getValue()));
		}
	}

	public void addPair(T t, U u) {
        Set<U> set = mBacking.get(t);
		if (set == null) {
			set = new HashSet<U>();
			mBacking.put(t, set);
		}
		set.add(u);
	}

	public Set<T> getDomain() {
		return mBacking.keySet();
	}

	public Set<U> getImage(T t) {
		return mBacking.get(t);
	}

	/**
	 * Checks if the represented relation is "rechtseindeutig" (right-unique?)
	 *  (strictly speaking this checks if it is a partial function)
	 * @return
	 */
	public boolean isFunction() {
		for (Entry<T, Set<U>> en : mBacking.entrySet()) {
			if (en.getValue().size() > 1) {
				return false;
			}
		}
		return true;
	}

	public Map<T, U> getFunction() {
		assert isFunction();
		Map<T, U> result =  new HashMap<T, U>();

		for (Entry<T, Set<U>> en : mBacking.entrySet()) {
			assert en.getValue().size() == 1 : "no function";
			result.put(en.getKey(), en.getValue().iterator().next());
		}
		return result;
	}

	public Set<T> getPreImage(U u) {
		Set<T> result = new HashSet<T>();
		//TODO: this could be sped up significantly by adding a "reverse" HashMap
		for (T d : getDomain()) {
			if (getImage(d).contains(u)) {
				result.add(d);
			}
		}
		return result;
	}

//	public Iterable<Pair<T, U>> getPairs() {
//		List<Pair<T, U>> result = new ArrayList<Pair<T, U>>();
//		for (T d : getDomain()) {
//			for (U im : getImage(d)) {
//				result.add(arg0)
//			}
//		}
//	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for (Entry<T, Set<U>> en : mBacking.entrySet()) {
			for (U el : en.getValue()) {
				sb.append("(" + en.getKey() + ", " + el + ")\n");
			}
		}
//		return mBacking.toString();
		return sb.toString();
	}

	public void removePair(T t, U u) {
		Set<U> image = mBacking.get(t);
		if (image != null) {
			image.remove(u);
		}
	}

	/**
	 * checks if this relation is left-unique or injective if it is a function..
	 * @return
	 */
	public boolean isInjective() {
		for (Entry<T, Set<U>> en1 : mBacking.entrySet()) {
			for (Entry<T, Set<U>> en2 : mBacking.entrySet()) {
				if (en1.equals(en2)) {
					continue;
				}
				final Set<U> intersection = new HashSet<U>(en1.getValue());
				intersection.retainAll(en2.getValue());

				if (!intersection.isEmpty()) {
					return false;
				}
			}
		}
		return true;
	}
}
