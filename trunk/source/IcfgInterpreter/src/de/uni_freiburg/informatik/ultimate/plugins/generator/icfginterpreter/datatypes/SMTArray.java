package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datatypes;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.NonDeterministicChoice;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;

public class SMTArray {
	private final HashMap<Object, Object> entries;
	public final Sort mKeySort;
	public final Sort mValueSort;
	public final Sort mSort;

	public SMTArray(final Sort sort) {
		this(new HashMap<>(), sort);
	}

	public SMTArray(final HashMap<Object, Object> mEntries, final Sort sort) {
		entries = mEntries;
		mKeySort = sort.getArguments()[0];
		mValueSort = sort.getArguments()[1];
		mSort = sort;
	}

	public Object select(final Object index, final NonDeterministicChoice ndc) {
		if (entries.containsKey(index)) {
			return entries.get(index);
		}
		return ndc.havocArrayEntry(this, index);
	}

	public SMTArray store(final Object index, final Object value) {
		final HashMap<Object, Object> mEntries = Util.copyMap(entries);
		mEntries.put(index, value);
		return new SMTArray(mEntries, mSort);
	}

	/**
	 * Used to optimize stacked store() calls, which would need to copy the full map for every call. <br>
	 * Stores the object at index 0 first, meaning later keys will overwrite equal ones earlier in the list.
	 */
	public SMTArray multiStore(final List<Object> keys, final List<Object> values) {
		assert keys.size() == values.size();

		final HashMap<Object, Object> mEntries = Util.copyMap(entries);
		for (int i = 0; i < keys.size(); i++) {
			mEntries.put(keys.get(i), values.get(i));
		}
		return new SMTArray(mEntries, mSort);
	}

	public HashMap<Object, Object> getEntries() {
		return Util.copyMap(entries);
	}

	@Override
	public String toString() {
		final StringBuilder out = new StringBuilder();
		out.append("[").append(mKeySort).append("]").append(mValueSort).append(" {");

		final ArrayList<String> lines = Util.map(entries.entrySet(), (entry) -> {
			return entry.getKey() + " -> " + entry.getValue();
		}, new ArrayList<String>());

		return out.append(String.join(", ", lines)).append("}").toString();
	}

	@Override
	public int hashCode() {
		return mSort.hashCode();
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof SMTArray)) {
			return false;
		}
		final SMTArray castB = (SMTArray) b;
		if ((!mKeySort.equals(castB.mKeySort)) || !mValueSort.equals(castB.mValueSort)) {
			return false;
		}
		// TODO ask ndc interface if equality holds if entries are the same
		return !entries.equals(castB.entries);
	}
}
