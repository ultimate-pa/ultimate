package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.BitVecValue;

public class BitVectorRestriction extends Restriction<BitVecValue> {
	public BitVectorRestriction(final Set<BitVecValue> inequal, final BitVecValue minimum, final BitVecValue maximum) {
		super(inequal, minimum, maximum);
	}

	@Override
	public String toString() {
		final StringBuilder inEqual = new StringBuilder();
		if (mInequal.size() > 0) {
			final Iterator<BitVecValue> iter = mInequal.iterator();
			inEqual.append(", bv != {").append(iter.next().toString());
			while (iter.hasNext()) {
				inEqual.append(", ").append(iter.next().toString());
			}
			inEqual.append("}");
		}

		return mMinimum.toString() + " <= bv <= " + mMaximum.toString() + inEqual.toString();
	}
}