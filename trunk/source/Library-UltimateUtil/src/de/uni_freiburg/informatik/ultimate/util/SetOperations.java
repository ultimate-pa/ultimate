package de.uni_freiburg.informatik.ultimate.util;

import java.util.HashSet;
import java.util.Set;

public class SetOperations {

	public static <T> Set<T> getFreshSet(final Set<T> oldSet, final int capacity) {
		final Set<T> rtr = new HashSet<>(capacity);
		rtr.addAll(oldSet);
		return rtr;
	}

	public static <T> Set<T> getFreshSet(final Set<T> oldSet) {
		return getFreshSet(oldSet, oldSet.size());
	}

	public static <T> Set<T> union(final Set<T> a, final Set<T> b) {
		final Set<T> rtr = getFreshSet(a, a.size() + b.size());
		rtr.addAll(b);
		return rtr;
	}

	public static <T> Set<T> intersect(final Set<T> a, final Set<T> b) {
		final Set<T> rtr = getFreshSet(a, a.size());
		rtr.retainAll(b);
		return rtr;
	}

	public static <T> Set<T> difference(final Set<T> a, final Set<T> b) {
		final Set<T> rtr = getFreshSet(a, a.size());
		rtr.removeAll(b);
		return rtr;
	}

}
