package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.ArrayValue;

public class ArrayRestriction extends Restriction<ArrayValue> {
	public ArrayRestriction(final Set<ArrayValue> inequal) {
		super(inequal, null, null);
	}

	@Override
	public String toString() {
		final StringBuilder inEqual = new StringBuilder();
		if (mInequal.size() > 0) {
			final Iterator<ArrayValue> iter = mInequal.iterator();
			inEqual.append("a != {").append(iter.next());
			while (iter.hasNext()) {
				inEqual.append(", ").append(iter.next());
			}
			inEqual.append("}");
		}

		return inEqual.toString();
	}
}