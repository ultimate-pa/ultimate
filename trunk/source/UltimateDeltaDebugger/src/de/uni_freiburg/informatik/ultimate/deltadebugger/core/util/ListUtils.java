package de.uni_freiburg.informatik.ultimate.deltadebugger.core.util;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;

public class ListUtils {
	private ListUtils() {
	}
	
	/**
	 * Computing the complement of the subsequence wrt. the given sequence.
	 * Important: subsequence must be a subsequence of universe (minimizer
	 * results guarantee that). Null elements are not supported.
	 * 
	 * @param subseqeuence
	 * @param universe
	 * @return complement
	 * @throws NoSuchElementException
	 *             if not actually a subsequence of universe
	 */
	public static <E> List<E> complementOfSubsequence(List<? extends E> subseqeuence, List<? extends E> universe) {
		if (subseqeuence.isEmpty()) {
			return Collections.unmodifiableList(universe);
		}
		if (subseqeuence.size() == universe.size()) {
			return Collections.emptyList();
		}
		final List<E> complement = new ArrayList<>(universe.size() - subseqeuence.size());
		final Iterator<? extends E> skipIter = subseqeuence.iterator();
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
