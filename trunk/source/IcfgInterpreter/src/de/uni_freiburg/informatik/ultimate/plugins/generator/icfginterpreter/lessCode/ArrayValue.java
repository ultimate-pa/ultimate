package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.NonDeterministicChoice;

public class ArrayValue implements Value {
	private final HashMap<Value, Value> mValue;
	private final String mUniqueIdentifier;
	private final Sort mSort;

	public ArrayValue(final HashMap<Value, Value> value, final String uniqueIdentifier, final Sort sort) {
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
	public BoolValue equals(final Value other) {
		if (other instanceof final ArrayValue av) {
			return new BoolValue(mValue.equals(av.mValue));
		}
		return new BoolValue(false);
	}

	@Override
	public BoolValue distinct(final Value other) {
		if (other instanceof final ArrayValue av) {
			return new BoolValue(!mValue.equals(av.mValue));
		}
		return new BoolValue(true);
	}

	@Override
	public HashMap<Value, Value> getValue() {
		return mValue;
	}
}