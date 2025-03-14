package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.SMTArray;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm.ReturnType;

public class ArrayDomain<keyType extends Domain<keyType>, valueType extends Domain<valueType>>
		implements Domain<ArrayDomain<keyType, valueType>> {
	// maps the domain containing some set keys to the
	// domain containing the values that this set of keys lead to
	private final HashMap<keyType, valueType> entries;
	private final ReturnType key;
	private final ReturnType value;

	public ArrayDomain(final HashMap<keyType, valueType> mEntries, final ReturnType mKey, final ReturnType mValue) {
		entries = mEntries;
		key = mKey;
		value = mValue;
	}

	private ArrayDomain() {
		key = null;
		value = null;
		entries = null;
	}

	public static ArrayDomain<?, ?> getEmptyDomain() {
		return new ArrayDomain<>();
	}

	public ArrayDomain<keyType, valueType> store(final keyType keys, final valueType values) {
		final HashMap<keyType, valueType> result = new HashMap<>();

		for (final Entry<keyType, valueType> entry : entries.entrySet()) {
			final keyType intersect = keys.intersection(entry.getKey());
			if (!intersect.isEmpty()) {
				// keep the keys that are exclusively in either set with their original values
				final keyType newExclusiveKeys = keys.difference(intersect);
				if (!newExclusiveKeys.isEmpty()) {
					result.put(newExclusiveKeys, values);
				}
				final keyType oldExclusiveKeys = entry.getKey().difference(intersect);
				if (!oldExclusiveKeys.isEmpty()) {
					result.put(oldExclusiveKeys, entry.getValue());
				}
				// the values of the intersecting keys can be either value
				// TODO does this make sense
				// result.put(intersect, values.union(entry.getValue()));
				// alt: overwrite affected values
				result.put(intersect, values);
			} else {
				// these keys are unchanged by the store usage
				result.put(entry.getKey(), entry.getValue());
			}
		}

		return new ArrayDomain<>(result, key, value);
	}

	public valueType select(final keyType keys) {
		valueType out = null;

		for (final Entry<keyType, valueType> entry : entries.entrySet()) {
			final keyType intersect = keys.intersection(entry.getKey());
			if (intersect.isEmpty()) {
				continue;
			}
			// if even one of the keys matches, any of the values of the key domain can appear
			if (out == null) {
				out = entry.getValue();
				continue;
			}
			out = out.union(entry.getValue());
		}

		return out;
	}

	@Override
	public ArrayDomain<keyType, valueType> union(final ArrayDomain<keyType, valueType> domain) {
		HashMap<keyType, valueType> result = Util.copyMap(entries);

		// shared keys unionize their values.
		// invariant: all entries of either set are disjoint from all other entries in their own set
		for (final Entry<keyType, valueType> entry : domain.entries.entrySet()) {
			final HashMap<keyType, valueType> temp = new HashMap<>();
			for (final Entry<keyType, valueType> other : result.entrySet()) {
				final keyType intersect = entry.getKey().intersection(other.getKey());
				if (intersect.isEmpty()) {
					// no keys are shared.
					temp.put(other.getKey(), other.getValue());
					continue;
				}

				// add combined values of shared keys
				temp.put(intersect, entry.getValue().union(other.getValue()));

				// add others original values for keys that only exist in other
				final keyType onlyOtherKeys = other.getKey().difference(intersect);
				if (onlyOtherKeys.isEmpty()) {
					continue;
				}
				temp.put(onlyOtherKeys, other.getValue());
				// we still have all the keys other had originally,
				// but we have split them into two sets to distinguish
				// the shared keys as a new set that contains values of both.
			}
			result = temp;
		}
		// all keys that are shared now have unionized values in temp.
		// all that remains is adding the keys that are exclusively in entry with their value.
		for (final Entry<keyType, valueType> entry : domain.entries.entrySet()) {
			keyType onlyEntryKeys = entry.getKey();

			for (final Entry<keyType, valueType> other : result.entrySet()) {
				onlyEntryKeys = onlyEntryKeys.complement(other.getKey());
			}

			if (onlyEntryKeys.isEmpty()) {
				continue;
			}
			result.put(onlyEntryKeys, entry.getValue());
		}

		return new ArrayDomain<>(result, key, value);
	}

	// gets the ArrayDomain that contains each (key, value) pair that appears in both sets
	@Override
	public ArrayDomain<keyType, valueType> intersection(final ArrayDomain<keyType, valueType> domain) {
		final HashMap<keyType, valueType> result = new HashMap<>();

		// invariant: all entries of either set are disjoint from all other entries in their own set
		for (final Entry<keyType, valueType> entry : entries.entrySet()) {
			for (final Entry<keyType, valueType> other : domain.entries.entrySet()) {
				final keyType intersectKeys = entry.getKey().intersection(other.getKey());

				if (intersectKeys.isEmpty()) {
					// no keys are shared.
					continue;
				}
				final valueType intersectValues = entry.getValue().intersection(other.getValue());
				if (intersectValues.isEmpty()) {
					// no values are shared.
					continue;
				}
				result.put(intersectKeys, intersectValues);
			}
		}
		return new ArrayDomain<>(result, key, value);
	}

	/**
	 * Gets the ArrayDomain that has all (key, value) pairs of this domain for which a (key, value) pair exists in the
	 * other domain where the key is the same but a different value is stored OR no (key, value) pair exists for the key
	 * in the other domain, meaning it could have any value
	 *
	 * @param domain
	 * @return
	 */
	@Override
	public ArrayDomain<keyType, valueType> complement(final ArrayDomain<keyType, valueType> domain) {
		HashMap<keyType, valueType> result = Util.copyMap(entries);

		for (final Entry<keyType, valueType> entry : domain.entries.entrySet()) {
			// Keeps all (key, value) pairs that appear in this domain but not the current subset of the other domain
			final HashMap<keyType, valueType> temp = new HashMap<>();
			for (final Entry<keyType, valueType> other : result.entrySet()) {
				// keys that appear in both sets
				final keyType intersectKeys = entry.getKey().intersection(other.getKey());
				// keys that appear only in this set
				final keyType uniqueKeys = entry.getKey().complement(intersectKeys);

				// if keys are shared, keep (key, value) pairs that are only in this set
				if (!intersectKeys.isEmpty()) {
					final valueType uniqueValues = entry.getValue().complement(other.getValue());
					if (!uniqueValues.isEmpty()) {
						temp.put(intersectKeys, uniqueValues);
					}
				}

				if (uniqueKeys.isEmpty()) {
					continue;
				}
				// for keys that appear only in this set, keep all values
				temp.put(uniqueKeys, entry.getValue());

			}
			result = temp;
		}

		return new ArrayDomain<>(result, key, value);
	}

	@Override
	public boolean contains(final Domain<?> domain) {
		if (!(domain instanceof ArrayDomain)) {
			return false;
		}
		final ArrayDomain<?, ?> domainCast = ((ArrayDomain<?, ?>) domain);
		assert key.equals(domainCast.key) && value.equals(domainCast.value);
		@SuppressWarnings("unchecked")
		final ArrayDomain<keyType, valueType> domainCastB = ((ArrayDomain<keyType, valueType>) domainCast);
		return domainCastB.complement(this).isEmpty();
	}

	// gets the ArrayDomain that, for each unique key set of either domain, contains the unique values
	@Override
	public ArrayDomain<keyType, valueType> difference(final ArrayDomain<keyType, valueType> domain) {
		final ArrayDomain<keyType, valueType> ANotInB = this.complement(domain);
		final ArrayDomain<keyType, valueType> BNotInA = domain.complement(this);
		return ANotInB.union(BNotInA);
	}

	@Override
	public ArrayList<Entry<Domain<?>, Domain<?>>> getValues() {
		final ArrayList<Entry<Domain<?>, Domain<?>>> out = new ArrayList<>();

		for (final Entry<keyType, valueType> entry : entries.entrySet()) {
			out.add(Map.entry(entry.getKey(), entry.getValue()));
		}

		return out;
	}

	@Override
	public boolean isEmpty() {
		return entries.size() == 0;
	}

	@Override
	public ReturnType getType() {
		return ReturnType.Array;
	}

	@Override
	public String toString() {
		final ArrayList<String> pairs = new ArrayList<>();
		for (final Entry<keyType, valueType> entry : entries.entrySet()) {
			pairs.add("\n" + entry.getKey() + " := " + entry.getValue());
		}
		return "{" + String.join("", pairs).replace("\n", "\n  ") + "\n}";
	}

	@Override
	public ArrayDomain<keyType, valueType> getFullDomain() {
		final HashMap<keyType, valueType> domain = new HashMap<>();
		// domain.put(key, value);
		return new ArrayDomain<>(domain, key, value);
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof ArrayDomain)) {
			return false;
		}
		final ArrayDomain<?, ?> bCast = (ArrayDomain<?, ?>) b;
		return entries.equals(bCast.entries);
	}

	@Override
	public ArrayDomain<keyType, valueType> domainFrom(final Object singleValue) {
		if (!(singleValue instanceof SMTArray)) {
			return new ArrayDomain<>();
		}
		@SuppressWarnings("unchecked")
		final HashMap<keyType, valueType> values = (HashMap<keyType, valueType>) ((SMTArray) singleValue).getEntries();
		return new ArrayDomain<>(values, key, value);
	}
}
