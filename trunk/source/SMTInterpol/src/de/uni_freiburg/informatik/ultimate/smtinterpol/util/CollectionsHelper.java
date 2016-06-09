/*
 * Copyright (C) 2009-2012 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.util;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

public final class CollectionsHelper {
	
	private CollectionsHelper() {
		// Hide constructor
	}
	/**
	 * Check whether <code>c2</code> contains any element in <code>c1</code>.
	 * @param <E> The type of the arguments.
	 * @param c1 Base collection against which we check.
	 * @param c2 Collection which should contain any of the elements in c1.
	 * @return <code>true</code> iff at least one element of <code>c1</code> is
	 * contained in <code>c2</code>.
	 */
	public static <E> boolean containsAny(Collection<E> c1,Collection<E> c2) {
		for (final E elem : c1) {
			if (c2.contains(elem)) {
				return true;
			}
		}
		return false;
	}
	/**
	 * Check whether <code>c2</code> contains any element in <code>c1</code>.
	 * @param <E> The type of the arguments.
	 * @param c1 Base collection against which we check.
	 * @param c2 Collection which should contain any of the elements in c1.
	 * @return <code>true</code> iff at least one element of <code>c1</code> is
	 * contained in <code>c2</code>.
	 */
	public static <E> boolean containsAny(E[] c1,Collection<E> c2) {
		for (final E elem : c1) {
			if (c2.contains(elem)) {
				return true;
			}
		}
		return false;
	}
	public static <E> Collection<E> asymmetricDifference(E[] c1,
			Collection<E> c2) {
		final Set<E> result = new HashSet<E>();
		for (final E elem : c1) {
			if (!c2.contains(elem)) {
				result.add(elem);
			}
		}
		return result;
	}	
}
