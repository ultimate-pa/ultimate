package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.BoolValue;

public class BooleanRestriction extends Restriction<BoolValue> {
	public BooleanRestriction(final Set<BoolValue> inequal) {
		super(inequal, null, null);
	}

	@Override
	public String toString() {
		final StringBuilder inEqual = new StringBuilder();
		if (mInequal.size() > 0) {
			final Iterator<BoolValue> iter = mInequal.iterator();
			inEqual.append("b != {").append(iter.next());
			while (iter.hasNext()) {
				inEqual.append(", ").append(iter.next());
			}
			inEqual.append("}");
		}

		return inEqual.toString();
	}
}