package de.uni_freiburg.informatik.ultimate.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

/**
 * Class containing a variety of combinatorial utility functions.
 * @author mostafa.amin93@gmail.com
 *
 */
public class CombinatoricsUtils {

	private CombinatoricsUtils() {}

	/***
	 * Transform an iterator to a set.
	 * @param iter
	 * @return
	 */
	public static <T> Set<T> iterateAll(final Iterator<T> iter) {
		final Set<T> res = new HashSet<>();
		while(iter.hasNext()) {
			res.add(iter.next());
		}
		return res;
	}

	/***
	 * Transform an iterator to a set.
	 * @param iter
	 * @return
	 */
	public static <T> Set<T> iterateAll(final Iterable<T> iter) {
		final Set<T> res = new HashSet<>();
		for (final T s : iter) {
			res.add(s);
		}
		return res;
	}
	
	/***
	 * Get all possible r-tuples combined by a set of different values for each field.
	 * @param values
	 * @return
	 */
	public static <T> Set<List<T>> getCombinations(final List<Collection<T>> values) {
		return getCombinations(values, values.size());
	}
	
	private static <T> Set<List<T>> getCombinations(final List<Collection<T>> values, int idx) {
		if (idx == 0) {
			final List<T> singleton = new ArrayList<>();
			final Set<List<T>> res = new HashSet<>();
			res.add(singleton);
			return res;
		}
		final Set<List<T>> oldCombinations = getCombinations(values, idx - 1);
		final Set<List<T>> res = new HashSet<>();
		for (final T newValue : values.get(idx - 1)) {
			for (final List<T> oldCombination : oldCombinations) {
				List<T> combination = new ArrayList<>();
				combination.addAll(oldCombination);
				combination.add(newValue);
				res.add(combination);
			}
		}
		return res;
	}
}
