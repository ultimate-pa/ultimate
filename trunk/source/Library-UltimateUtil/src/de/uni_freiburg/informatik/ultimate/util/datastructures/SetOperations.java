/*
 * Copyright (C) 2018 Claus Schaetzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

/**
 * Set operations like union and intersection.
 * Methods ending with "multi" work like multiset operation in case the result collection allows for duplicates.
 * <p>
 * For a method to check whether two collections are disjoint see
 * {@link Collections#disjoint(Collection, Collection)}.
 * 
 * @author schaetzc@tf.uni-freiburg.de
 */
public final class SetOperations {

	private SetOperations() {
		// No need for objects of this class.
		// Class contains only static methods.
	}
	
	public static <E, C extends Collection<E>> C intersection(final C result,
			final Collection<? extends E> setA, final Collection<? extends E> setB) {
		result.addAll(setA);
		result.retainAll(setB);
		return result;
	}
	
	public static <E> Set<E> intersection(
			final Collection<? extends E> setA, final Collection<? extends E> setB) {
		final Set<E> result = new HashSet<>(setA); 
		result.retainAll(setB);
		return result;
	}
	
	public static <E, C extends Collection<E>> C unionMulti(final C result,
			final Collection<? extends E> setA, final Collection<? extends E> setB) {
		result.addAll(setA);
		result.addAll(setB);
		return result;
	}
	
	public static <E> Set<E> union(
			final Collection<? extends E> setA, final Collection<? extends E> setB) {
		final Set<E> result = new HashSet<>(setA); 
		result.addAll(setB);
		return result;
	}
	
	public static <E, C extends Collection<E>> C difference(final C result,
			final Collection<? extends E> minuend, final Collection<? extends E> subtrahend) {
		result.addAll(minuend);
		result.removeAll(subtrahend);
		return result;
	}
	
	public static <E> Set<E> difference(
			final Collection<? extends E> minuend, final Collection<? extends E> subtrahend) {
		final Set<E> result = new HashSet<>(minuend);
		result.removeAll(subtrahend);
		return result;
	}
	
	public static <E> boolean disjoint(
			final Collection<? extends E> set1, final Collection<? extends E> set2) {
		return Collections.disjoint(set1, set2);
	}
	
	public static <E> boolean intersecting(
			final Collection<? extends E> set1, final Collection<? extends E> set2) {
		return !Collections.disjoint(set1, set2);
	}
}


