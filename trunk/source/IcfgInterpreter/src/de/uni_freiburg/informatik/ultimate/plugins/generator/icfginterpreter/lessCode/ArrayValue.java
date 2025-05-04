package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.NonDeterministicChoice;

public class ArrayValue implements Value {
	private final Map<Value, Value> mValue;
	private final String mUniqueIdentifier;
	private final Sort mSort;

	public ArrayValue(final Map<Value, Value> value, final String uniqueIdentifier, final Sort sort) {
		mValue = value;
		mUniqueIdentifier = uniqueIdentifier;
		mSort = sort;
	}

	public ArrayValue store(final Value key, final Value value) {
		final HashMap<Value, Value> out = new HashMap<>(mValue);
		out.put(key, value);
		return new ArrayValue(out, mUniqueIdentifier, mSort);
	}

	public Value select(final Value key, final NonDeterministicChoice ndc) {
		if (mValue.containsKey(key)) {
			return mValue.get(key);
		}
		// TODO change NDC to return Value once this implementation is the only one used
		// final Object value = ndc.havocArrayEntry(mSort, mUniqueIdentifier, key);
		return null;
	}

	@Override
	public BoolValue distinct(final Value other) {
		if (other instanceof final ArrayValue av) {
			return new BoolValue(!mValue.equals(av.mValue));
		}
		return BoolValue.mTrue;
	}

	@Override
	public Map<Value, Value> getValue() {
		return mValue;
	}

	@Override
	public String toString() {
		final ArrayList<Entry<Value, Value>> list = new ArrayList<>(mValue.entrySet());

		Collections.sort(list, (entry1, entry2) -> entry1.getKey().compareTo(entry2.getKey()));

		final List<String> lines = list.stream().map((entry) -> entry.getKey() + " -> " + entry.getValue()).toList();

		return new StringBuilder("{").append(String.join(", ", lines)).append("}").toString();
	}

	@Override
	public Term toTerm(final Script script) {
		return null;
		// TODO convert arrays
	}

	@Override
	public BoolValue equals(final Value other) {
		if (other instanceof final ArrayValue av) {
			return new BoolValue(mValue.equals(av.mValue));
		}
		return BoolValue.mFalse;
	}

	@Override
	public boolean equals(final Object b) {
		if (b instanceof final ArrayValue av) {
			return mValue.equals(av.mValue);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return mValue.hashCode();
	}

	@Override
	public int compareTo(final Value b) {
		if (b instanceof final ArrayValue av) {
			// TODO find better way that is consistent
			return Integer.compare(mValue.size(), av.mValue.size());
		}
		return this.getClass().getSimpleName().compareTo(b.getClass().getSimpleName());
	}

	public Sort getSort() {
		return mSort;
	}

	public String getUniqueIdentifier() {
		return mUniqueIdentifier;
	}
}