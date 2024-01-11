/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 *         TODO: Merge {@link SetOperations} in this class.
 */
public class DataStructureUtils {

	private DataStructureUtils() {
		// do not instantiate
	}

	/**
	 * Constructs a new {@link Set} that contains only elements that occur in set1 and that occur in set2.
	 */
	public static <T> Set<T> intersection(final Set<T> set1, final Set<T> set2) {
		final Set<T> larger;
		final Set<T> smaller;
		if (set1.size() > set2.size()) {
			larger = set1;
			smaller = set2;
		} else {
			larger = set2;
			smaller = set1;
		}
		return smaller.stream().filter(larger::contains).collect(Collectors.toSet());
	}

	/**
	 * Constructs a new {@link Set} that contains only elements that occur in all sets that are in the list inputSets.
	 * Modifies the list inputSets but not the contained sets.
	 */
	public static <T> Set<T> intersection(final List<Set<T>> inputSets) {
		Collections.sort(inputSets, (o1, o2) -> o1.size() - o2.size());
		Set<T> result;
		final Iterator<Set<T>> it = inputSets.iterator();
		result = new HashSet<>(it.next());
		while (it.hasNext()) {
			result.retainAll(it.next());
		}
		return result;
	}

	/**
	 * @return an Optional<T> that contains an element that is contained in both sets or is empty if both sets do not
	 *         have a common element.
	 */
	public static <T> Optional<T> getSomeCommonElement(final Set<T> set1, final Set<T> set2) {
		if (set1.isEmpty() || set2.isEmpty()) {
			// at least one is empty, there is no common element
			return Optional.empty();
		}
		final Set<T> larger;
		final Set<T> smaller;
		if (set1.size() > set2.size()) {
			larger = set1;
			smaller = set2;
		} else {
			larger = set2;
			smaller = set1;
		}
		return smaller.stream().filter(larger::contains).findFirst();
	}

	/**
	 * Construct a {@link Set} that contains all elements of set1 that are not in set2.
	 *
	 * The returned set is not guaranteed to be mutable.
	 *
	 * Future changes to the sets a and b will not be reflected in the returned set.
	 */
	public static <T> Set<T> difference(final Set<T> a, final Set<T> b) {
		if (a.isEmpty()) {
			return Collections.emptySet();
		}
		if (b.isEmpty()) {
			if (a instanceof ImmutableSet<?>) {
				return a;
			}
			return new HashSet<>(a);
		}
		return a.stream().filter(elem -> !b.contains(elem)).collect(Collectors.toSet());
	}

	@SafeVarargs
	public static <T> Set<T> toSet(final T... elems) {
		if (elems == null || elems.length == 0) {
			return Collections.emptySet();
		}
		return new HashSet<>(Arrays.asList(elems));
	}

	/**
	 * Construct a {@link Set} that contains all elements of set1 and set2.
	 */
	public static <T> Set<T> union(final Set<T> a, final Set<T> b) {
		final Set<T> rtr = DataStructureUtils.getFreshSet(a, a.size() + b.size());
		rtr.addAll(b);
		return rtr;
	}

	@SafeVarargs
	public static <T> Set<T> union(final Set<T>... a) {
		if (a.length == 0) {
			return Collections.emptySet();
		}

		final int size = Arrays.stream(a).mapToInt(Set::size).sum();

		final Set<T> rtr = DataStructureUtils.getFreshSet(a[0], size);
		Arrays.stream(a).forEach(rtr::addAll);
		return rtr;
	}

	/**
	 * Construct a {@link Set} that contains all elements of oldSet and has the capacity of oldSet.
	 */
	public static <T> Set<T> getFreshSet(final Set<T> oldSet) {
		return DataStructureUtils.getFreshSet(oldSet, oldSet.size());
	}

	/**
	 * Construct a {@link Set} that contains all elements of oldSet and starts with an initial capacity.
	 */
	public static <T> Set<T> getFreshSet(final Set<T> oldSet, final int capacity) {
		final Set<T> rtr = new HashSet<>(capacity);
		rtr.addAll(oldSet);
		return rtr;
	}

	/**
	 * Returns true, if the given sets have at least one common element.
	 *
	 * Should be quicker than first computing the intersection and the calling isEmpty() on it.
	 *
	 * @param set1
	 * @param set2
	 * @return
	 */
	public static <T> boolean haveNonEmptyIntersection(final Set<T> set1, final Set<T> set2) {
		final Set<T> larger;
		final Set<T> smaller;
		if (set1.size() > set2.size()) {
			larger = set1;
			smaller = set2;
		} else {
			larger = set2;
			smaller = set1;
		}
		return smaller.stream().anyMatch(larger::contains);
	}

	/**
	 * @return Both sets are disjoint
	 */
	public static <T> boolean haveEmptyIntersection(final Set<T> set1, final Set<T> set2) {
		return !haveNonEmptyIntersection(set1, set2);
	}

	/**
	 * Returns true, if the given collection and set have at least one common
	 * element.
	 */
	public static <T> boolean haveNonEmptyIntersection(final Collection<T> collection, final Set<T> set) {
		return collection.stream().anyMatch(set::contains);
	}

	/**
	 * @return The collection and the set are disjoint
	 */
	public static <T> boolean haveEmptyIntersection(final Collection<T> collection, final Set<T> set) {
		return !haveNonEmptyIntersection(collection, set);
	}

	public static <E> String prettyPrint(final Set<E> set) {
		final StringBuilder sb = new StringBuilder();
		sb.append("Set: \n");
		String sep = "";
		for (final E e : set) {
			sb.append(sep);
			sb.append(String.format("\t%s", e));
			sep = "\n";
		}
		return sb.toString();
	}

	public static <K, V> String prettyPrint(final Map<K, V> map) {
		// TODO: implement a width check for the keys, adapt column with, and/or cut their size at some length
		final StringBuilder sb = new StringBuilder();
		sb.append("Map: \n");
		String sep = "";
		for (final Entry<K, V> en : map.entrySet()) {
			sb.append(sep);
			sb.append(String.format("\t%-80s : \t %s", en.getKey(), en.getValue()));
			sep = "\n";
		}
		return sb.toString();
	}

	public static <K1, K2, V> String prettyPrint(final NestedMap2<K1, K2, V> map) {
		final StringBuilder sb = new StringBuilder();
		sb.append("NestedMap2: \n");
		String sep = "";
		for (final Triple<K1, K2, V> en : map.entrySet()) {
			sb.append(sep);
			sb.append(String.format("\t%-80s : \t %-40s : \t %s", en.getFirst(), en.getSecond(), en.getThird()));
			sep = "\n";
		}
		return sb.toString();
	}

	@SuppressWarnings("unchecked")
	public static <T> T[] concat(final T[] a1, final T[] a2) {
		if (a1 == null) {
			return a2;
		}
		if (a2 == null) {
			return a1;
		}
		if (a1.length == 0) {
			return a2;
		}
		if (a2.length == 0) {
			return a1;
		}
		final T[] dest = (T[]) Array.newInstance(a1.getClass().getComponentType(), a1.length + a2.length);
		System.arraycopy(a1, 0, dest, 0, a1.length);
		System.arraycopy(a2, 0, dest, a1.length, a2.length);
		return dest;
	}

	public static <T> List<T> concat(final List<T> a1, final List<T> a2) {
		if (a1 == null) {
			return a2;
		}
		if (a2 == null) {
			return a1;
		}
		if (a1.isEmpty()) {
			return a2;
		}
		if (a2.isEmpty()) {
			return a1;
		}
		final List<T> rtr = new ArrayList<>(a1.size() + a2.size() + 1);
		rtr.addAll(a1);
		rtr.addAll(a2);
		return rtr;
	}

	/**
	 * Rather naive powerset implementation
	 *
	 * @param baseSet
	 * @return
	 */
	public static <T> Collection<Set<T>> powerSet(final Set<T> baseSet) {
		final Collection<Set<T>> result = new ArrayList<>();

		final List<T> baseList = new ArrayList<>(baseSet);

		final double pow = Math.pow(2, baseSet.size());

		for (int bin = 0; bin < pow; bin++) {

			final Set<T> subset = new HashSet<>();

			// note that this char array always starts with a 1 (obviously) somehow, so we have to "fill up" leading 0s
			final char[] binS = Integer.toBinaryString(bin).toCharArray();

			for (int pos = 0; pos < binS.length; pos++) {
				if (binS[pos] == '1') {
					subset.add(baseList.get(pos + baseSet.size() - binS.length));

				} else {
					assert binS[pos] == '0';
				}
			}
			result.add(subset);
		}

		return result;
	}

	/**
	 * Construct Map<V, K> that contains a pair (v,k) in the input contained the pair (k,v). If the input is not
	 * injective the behavior is not specified.
	 */
	public static <K, V> Map<V, K> constructReverseMapping(final Map<K, V> map) {
		return map.entrySet().stream().collect(Collectors.toMap(Map.Entry::getValue, Map.Entry::getKey));
	}

	/**
	 *
	 * @return true iff both sets consist of the same elements or are empty, false otherwise.
	 */
	public static <E> boolean isDifferent(final Set<E> a, final Set<E> b) {
		if (a.isEmpty() && b.isEmpty()) {
			return false;
		}
		if (a.size() != b.size()) {
			return true;
		}
		return a.stream().anyMatch(e -> !b.contains(e));
	}

	public static <T> boolean differenceIsEmpty(final T[] a, final T[] b) {
		if (a == null || a.length == 0) {
			return true;
		}
		if (b == null || b.length == 0) {
			return false;
		}
		final Set<T> setB = new HashSet<>(Arrays.asList(b));
		for (int i = 0; i < a.length; ++i) {
			if (!setB.contains(a[i])) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Adds all suffixes from <code>suffix</code> to the prefixes from <code>prefix</code>, i.e.
	 *
	 * <code>
	 * crossProduct([[A1,B1], [A2,B2]], [[C1,D1], [C2,D2]])
	 * </code> returns <code>
	 * [[A1,B1,C1,D1],[A1,B1,C2,D2] [A2,B2,C1,D1],[A2,B2,C2,D2]]
	 * </code>
	 *
	 */
	public static <T> List<List<T>> crossProduct(final List<List<T>> prefix, final List<List<T>> suffix) {
		if (prefix.isEmpty()) {
			return suffix;
		}
		if (suffix.isEmpty()) {
			return prefix;
		}
		final List<List<T>> rtr = new ArrayList<>(prefix.size() * suffix.size());
		for (final List<T> p : prefix) {
			for (final List<T> s : suffix) {
				rtr.add(concat(p, s));
			}
		}
		return rtr;
	}

	/**
	 * Gets an element from a given {@link Iterable}, and checks (with assertions) that this element is the only one.
	 *
	 * @param <E>
	 *            The type of elements
	 *
	 * @param elements
	 *            The {@link Iterable} from which the first element is retrieved.
	 * @param thing
	 *            A string describing the kind of element that is retrieved. Used in the assertion error messages
	 * @return The first (and only) element
	 */
	public static <E> E getOneAndOnly(final Iterable<E> elements, final String thing) {
		final Iterator<E> iterator = elements.iterator();
		assert iterator.hasNext() : "Must have at least one " + thing;
		final E elem = iterator.next();
		assert !iterator.hasNext() : "Only one " + thing + " allowed";
		return elem;
	}

	/**
	 * Gets an element from a given {@link Iterable}, if there is one. Also checks (with assertions) that there are not
	 * more than one elements.
	 *
	 * @param <E>
	 *            The type of elements
	 *
	 * @param elements
	 *            The {@link Iterable} from which the first element is retrieved.
	 * @param errMsg
	 *            An error message used in the assertion that there are not more elements
	 * @return The first (and only) element, if there is one
	 */
	public static <E> Optional<E> getOnly(final Iterable<E> elements, final String errMsg) {
		final Iterator<E> iterator = elements.iterator();
		if (!iterator.hasNext()) {
			return Optional.empty();
		}
		final E elem = iterator.next();
		assert !iterator.hasNext() : errMsg;
		return Optional.of(elem);
	}

	public static <E> Stream<E> filteredCast(final Stream<?> s, final Class<E> c) {
		return s.filter(a -> c.isAssignableFrom(a.getClass())).map(c::cast);
	}

	/**
	 * Converts a stream into an unmodifiable set (as returned by {@link Set#of()}.
	 *
	 * @param <T>
	 *            The type of elements
	 * @param stream
	 *            a stream of elements
	 * @return the set
	 *
	 * @throws IllegalArgumentException
	 *             if the stream contains multiple occurrences of the same element
	 */
	public static <T> Set<T> asSet(final Stream<T> stream) {
		final Object[] elements = stream.toArray();
		return (Set<T>) Set.of(elements);
	}

	/**
	 * Return an unmodifiable view of the input set. Use
	 * {@link Collections#emptySet} or {@link Collections#singleton} if possible to
	 * get a memory-efficient representation.
	 */
	public static <T> Set<T> getUnmodifiable(final Set<T> set) {
		if (set.isEmpty()) {
			return Collections.emptySet();
		} else if (set.size() == 1) {
			return Collections.singleton(set.iterator().next());
		} else {
			return Collections.unmodifiableSet(set);
		}
	}


	/**
	 * Construct a new {@link ArrayList} that is a almost a copy of the input list
	 * but where one given index is missing.
	 *
	 */
	public static <E> List<E> copyAllButOne(final List<E> list, final int indexToBeRemoved) {
		if (indexToBeRemoved < 0 || indexToBeRemoved >= list.size()) {
			throw new IllegalArgumentException("Index where we remove must be inside array");
		}
		final List<E> result = new ArrayList<>(list.size() -1);
		int i = 0;
		for (final E elem : list) {
			if (i != indexToBeRemoved) {
				result.add(elem);
			}
			i++;
		}
		assert i == list.size();
		assert result.size() == list.size() - 1;
		return result;
	}
}
