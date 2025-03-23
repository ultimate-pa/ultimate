package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.util.ArrayList;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm.ReturnType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array.VariableArrayTerm;

public class SMTArray {
	private final HashMap<Object, Object> entries;
	public final ReturnType keyType, valueType;
	public final VariableArrayTerm variable;

	public SMTArray(final ReturnType mKeyType, final ReturnType mValueType, final VariableArrayTerm arrayVar) {
		entries = new HashMap<>();
		valueType = mValueType;
		keyType = mKeyType;
		variable = arrayVar;
	}

	private SMTArray(final HashMap<Object, Object> mEntries, final ReturnType mKeyType, final ReturnType mValueType,
			final VariableArrayTerm mVariable) {
		entries = mEntries;
		valueType = mValueType;
		keyType = mKeyType;
		variable = mVariable;
	}

	public Object select(final Object index, final ProgramState currentState) {
		if (entries.containsKey(index)) {
			return entries.get(index);
		}
		return currentState.getNDC().havocArrayEntry(this, index);
	}

	public SMTArray store(final Object index, final Object value) {
		final HashMap<Object, Object> mEntries = Util.copyMap(entries);
		mEntries.put(index, value);
		return new SMTArray(mEntries, keyType, valueType, variable);
	}

	public HashMap<Object, Object> getEntries() {
		return Util.copyMap(entries);
	}

	@Override
	public String toString() {
		final StringBuilder out = new StringBuilder();
		out.append("[").append(keyType).append("]").append(valueType).append(" {");

		final ArrayList<String> lines = Util.map(entries.entrySet(), (entry) -> {
			return entry.getKey() + " -> " + entry.getValue();
		}, new ArrayList<String>());

		return out.append(String.join(", ", lines)).append("}").toString();
	}
}
