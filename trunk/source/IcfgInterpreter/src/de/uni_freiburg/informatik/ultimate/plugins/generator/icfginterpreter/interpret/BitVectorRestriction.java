package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.BitVector;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;

public class BitVectorRestriction extends Restriction<BitVector> {
	public BitVectorRestriction(final HashSet<BitVector> inequal, final BitVector less, final BitVector greater) {
		super(inequal, less, greater);
	}

	@Override
	public String toCode() {
		return "new " + this.getClass().getSimpleName() + "(Util.toHashSet("
				+ String.join(", ", Util.map(mInequal, (inequal) -> {
					return inequal.toString();
				}, new ArrayList<>())) + "), " + mLess + ", " + mGreater + ")";
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

		return mGreater.valueString() + " < bv < " + mLess.valueString() + inEqual.toString();
	}
}