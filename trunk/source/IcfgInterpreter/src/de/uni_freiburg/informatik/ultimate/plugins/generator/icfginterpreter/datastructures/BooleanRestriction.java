package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datastructures;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

public class BooleanRestriction extends Restriction<BoolValue> {
	public BooleanRestriction(final Set<BoolValue> inequal) {
		super(inequal, null, null);
	}

	@Override
	public String toString() {
		final StringBuilder inEqual = new StringBuilder();
		if (!mInequal.isEmpty()) {
			final Iterator<BoolValue> iter = mInequal.iterator();
			inEqual.append("b != {").append(iter.next());
			while (iter.hasNext()) {
				inEqual.append(", ").append(iter.next());
			}
			inEqual.append("}");
		}

		return inEqual.toString();
	}

	@Override
	public BooleanRestriction combine(final Restriction<?> other) {
		if (other instanceof final BooleanRestriction br) {
			final HashSet<BoolValue> inEquals = new HashSet<>(mInequal);
			inEquals.addAll(br.mInequal);
			return new BooleanRestriction(inEquals);
		}
		return this;
	}
}