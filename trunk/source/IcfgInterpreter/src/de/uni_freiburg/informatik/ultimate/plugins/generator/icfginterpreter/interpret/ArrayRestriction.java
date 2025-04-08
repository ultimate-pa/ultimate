package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.SMTArray;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;

public class ArrayRestriction extends Restriction<SMTArray> {
	public ArrayRestriction(final HashSet<SMTArray> inequal) {
		super(inequal, null, null);
	}

	@Override
	public String toCode() {
		return "new " + this.getClass().getSimpleName() + "(Util.toHashSet("
				+ String.join(", ", Util.map(mInequal, (inequal) -> {
					return inequal.toString();
				}, new ArrayList<>()));
	}

	@Override
	public String toString() {
		final StringBuilder inEqual = new StringBuilder();
		if (mInequal.size() > 0) {
			final Iterator<SMTArray> iter = mInequal.iterator();
			inEqual.append("a != {").append(iter.next());
			while (iter.hasNext()) {
				inEqual.append(", ").append(iter.next());
			}
			inEqual.append("}");
		}

		return inEqual.toString();
	}
}