package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datatypes.BitVector;

public class BitVectorRestriction extends Restriction<BitVector> {
	public BitVectorRestriction(final HashSet<BitVector> inequal, final BitVector minimum, final BitVector maximum) {
		super(inequal, minimum, maximum);
	}

	@Override
	public String toCode() {
		return "new " + this.getClass().getSimpleName() + "(Util.toHashSet("
				+ String.join(", ", Util.map(mInequal, (inequal) -> {
					return inequal.toString();
				}, new ArrayList<>())) + "), " + mMinimum + ", " + mMaximum + ")";
	}

	@Override
	public String toString() {
		final StringBuilder inEqual = new StringBuilder();
		if (mInequal.size() > 0) {
			final Iterator<BitVector> iter = mInequal.iterator();
			inEqual.append(", bv != {").append(iter.next().valueString());
			while (iter.hasNext()) {
				inEqual.append(", ").append(iter.next().valueString());
			}
			inEqual.append("}");
		}

		return mMinimum.valueString() + " <= bv <= " + mMaximum.valueString() + inEqual.toString();
	}
}