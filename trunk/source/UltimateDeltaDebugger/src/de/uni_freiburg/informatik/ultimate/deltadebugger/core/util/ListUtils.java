/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.util;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

/**
 * List utility class.
 */
public final class ListUtils {
	private ListUtils() {
		// utility class
	}
	
	/**
	 * Computing the complement of the subsequence wrt. the given sequence.<br>
	 * Important: subsequence must be a subsequence of universe (minimizer results guarantee that). Null elements are
	 * not supported.
	 *
	 * @param subsequence
	 *            subsequence
	 * @param universe
	 *            universe
	 * @param <E>
	 *            list element type
	 * @return complement
	 */
	public static <E> List<E> complementOfSubsequence(final List<? extends E> subsequence,
			final List<? extends E> universe) {
		if (subsequence.isEmpty()) {
			return Collections.unmodifiableList(universe);
		}
		if (subsequence.size() == universe.size()) {
			return Collections.emptyList();
		}
		final List<E> complement = new ArrayList<>(universe.size() - subsequence.size());
		final Iterator<? extends E> skipIter = subsequence.iterator();
		final Iterator<? extends E> sourceIter = universe.iterator();
		while (skipIter.hasNext()) {
			final E nextToSkip = skipIter.next();
			while (true) {
				final E element = sourceIter.next();
				if (nextToSkip.equals(element)) {
					break;
				}
				complement.add(element);
			}
		}
		
		while (sourceIter.hasNext()) {
			complement.add(sourceIter.next());
		}
		
		return complement;
	}
}
