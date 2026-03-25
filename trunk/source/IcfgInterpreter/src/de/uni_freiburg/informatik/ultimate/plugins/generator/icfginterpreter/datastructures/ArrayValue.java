package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datastructures;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class ArrayValue implements Value {
	private final TermVariable mArrayVar;
	private final HashMap<List<Value>, Value> mValue;
	private final Sort mSort;
	private final Sort mValueSort;

	public static class EmptyArrayEntryException extends AssertionError {
		private static final long serialVersionUID = 1L;

		public EmptyArrayEntryException(final String text) {
			super(text);
		}
	}

	public ArrayValue(final HashMap<List<Value>, Value> value, final TermVariable arrayVar) {
		mValue = value;
		mArrayVar = arrayVar;
		mSort = mArrayVar.getSort();
		// While arraySort is (Array Key Value), set arraySort := Value
		// In the end, we will have found the Sort of the stored values
		Sort arraySort = mSort;
		while (arraySort.isArraySort()) {
			arraySort = arraySort.getArguments()[1];
		}
		mValueSort = arraySort;
	}

	public ArrayValue store(final List<Value> key, final Value value) {
		@SuppressWarnings("unchecked")
		final HashMap<List<Value>, Value> out = (HashMap<List<Value>, Value>) mValue.clone();
		out.put(key, value);
		return new ArrayValue(out, mArrayVar);
	}

	public Value select(final List<Value> key) {
		final Value value = mValue.get(key);
		if (value == null) {
			throw new EmptyArrayEntryException("Array does not contain key " + key.toString());
		}
		return value;
	}

	public boolean hasKey(final List<Value> key) {
		return mValue.containsKey(key);
	}

	@Override
	public BoolValue distinct(final Value other) {
		if (other instanceof final ArrayValue av) {
			return new BoolValue(!mValue.equals(av.mValue));
		}
		return BoolValue.TRUE;
	}

	@Override
	public Map<List<Value>, Value> getValue() {
		return mValue;
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder(mArrayVar.getName() + "{");

		String seperator = "";
		for (final Entry<List<Value>, Value> entry : mValue.entrySet()) {
			builder.append(seperator);
			seperator = "; ";
			for (final Value key : entry.getKey()) {
				builder.append("[").append(key.toString()).append("]");
			}
			builder.append(" = ").append(entry.getValue());
		}

		return builder.append("}").toString();
	}

	@Override
	public Map<Term, Term> toTerm(final Script script, final Term var) {
		final Map<Term, Term> out = new HashMap<>();
		for (final Entry<List<Value>, Value> entry : mValue.entrySet()) {

			final Term valueTerm = entry.getValue().toTerm(script, var).get(var);

			Term select = var;
			for (final Value key : entry.getKey()) {
				select = SmtUtils.select(script, select, key.toTerm(script, var).get(var));
			}

			out.put(select, valueTerm);
		}

		return out;
	}

	@Override
	public BoolValue equals(final Value other) {
		if (other instanceof final ArrayValue av) {
			return new BoolValue(mValue.equals(av.mValue));
		}
		return BoolValue.FALSE;
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

	public TermVariable getTermVar() {
		return mArrayVar;
	}

	public Sort getSort() {
		return mSort;
	}

	public Sort getValueSort() {
		return mValueSort;
	}
}