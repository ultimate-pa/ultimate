package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.NonDeterministicChoice;

public class ArrayValue implements Value {
	private final Map<Value, Value> mValue;
	private final Sort mSort;

	public ArrayValue(final Map<Value, Value> value, final Sort sort) {
		mValue = value;
		mSort = sort;
	}

	public ArrayValue store(final Value key, final Value value) {
		final HashMap<Value, Value> out = new HashMap<>(mValue);
		out.put(key, value);
		return new ArrayValue(out, mSort);
	}

	public Value select(final Value key, final NonDeterministicChoice ndc) {
		if (mValue.containsKey(key)) {
			return mValue.get(key);
		}
		final Sort valueSort = mSort.getArguments()[1];
		final Value out = ndc.havoc(valueSort, null);
		// TODO Update state to add havoced entries in previous iterations
		mValue.put(key, out);
		return out;
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

		Collections.sort(list, Comparator.comparing(Entry<Value, Value>::getKey));

		final List<String> lines = list.stream().map((entry) -> entry.getKey() + " -> " + entry.getValue()).toList();

		return new StringBuilder("{").append(String.join(", ", lines)).append("}").toString();
	}

	@Override
	public Term toTerm(final Script script) {
		return null;
		// TODO convert arrays
	}

	public Map<Term, Term> makeOutValues(final Script script, final Term array) {
		final Map<Term, Term> arrayValues = new HashMap<>();// new Term[mValue.size()];

		for (final Entry<Value, Value> value : mValue.entrySet()) {
			final Term selectIndex = SmtUtils.select(script, array, value.getKey().toTerm(script));
			arrayValues.put(selectIndex, value.getValue().toTerm(script));
		}

		return arrayValues;
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
}