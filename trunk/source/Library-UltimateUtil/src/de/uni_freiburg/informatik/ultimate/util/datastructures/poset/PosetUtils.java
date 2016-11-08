/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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

import java.util.Collection;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator.ComparisonResult;

/**
 * Provides static methods for partially ordered sets.
 * @author Matthias Heizmann
 *
 */
public class PosetUtils {
	
	/**
	 * Return true iff there is no element in allElement that is strictly
	 * greater than element with respect to {@link IPartialComparator} comp.
	 */
	public static <T> boolean isMaximalElement(final T elem, final Stream<T> allElems, final IPartialComparator<T> comp) {
		final boolean result = allElems.allMatch(x -> comp.compare(x, elem) != ComparisonResult.STRICTLY_GREATER);
		return result;
	}
	
	/**
	 * Return true iff there is no element in allElement that is strictly
	 * smaller than element with respect to {@link IPartialComparator} comp.
	 */
	public static <T> boolean isMinimalElement(final T eleme, final Stream<T> allElems, final IPartialComparator<T> comp) {
		final boolean result = allElems.allMatch(x -> comp.compare(x, eleme) != ComparisonResult.STRICTLY_SMALLER);
		return result;
	}
	
	/**
	 * Returns a Stream that contains only the maximal elements with respect to 
	 * {@link IPartialComparator} comp.
	 */
	public static <T> Stream<T> filterMaximalElements(final Collection<T> allElems, final IPartialComparator<T> comp) {
		return allElems.stream().filter(x -> isMaximalElement(x, allElems.stream(), comp));
	}

	/**
	 * Returns a Stream that contains only the minimal elements with respect to 
	 * {@link IPartialComparator} comp.
	 */
	public static <T> Stream<T> filterMinimalElements(final Collection<T> allElems, final IPartialComparator<T> comp) {
		return allElems.stream().filter(x -> isMinimalElement(x, allElems.stream(), comp));
	}


	
}
