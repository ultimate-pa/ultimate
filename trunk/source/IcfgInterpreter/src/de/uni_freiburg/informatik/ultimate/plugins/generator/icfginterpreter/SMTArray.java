package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.util.ArrayList;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Sort;

public class SMTArray {
	private final HashMap<Object, Object> entries;
	public final Sort mKeySort;
	public final Sort mValueSort;
	public final IProgramVar mVariable;

	public SMTArray(final IProgramVar variable) {
		this(new HashMap<>(), variable);
	}

	private SMTArray(final HashMap<Object, Object> mEntries, final IProgramVar variable) {
		entries = mEntries;
		mKeySort = variable.getSort().getArguments()[0];
		mValueSort = variable.getSort().getArguments()[1];
		mVariable = variable;
	}

	public SMTArray(final HashMap<Object, Object> mEntries, final IProgramVar variable, final Sort keySort,
			final Sort valueSort) {
		entries = mEntries;
		mKeySort = keySort;
		mValueSort = valueSort;
		mVariable = variable;
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
		return new SMTArray(mEntries, mVariable, mKeySort, mValueSort);
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
		return ((mVariable.hashCode() * 31) + mKeySort.hashCode()) * 31 + mValueSort.hashCode();
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
