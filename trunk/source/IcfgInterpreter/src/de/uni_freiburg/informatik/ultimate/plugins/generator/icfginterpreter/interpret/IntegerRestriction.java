package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;

public class IntegerRestriction extends Restriction<Integer> {
	private final int mValueCount;

	/**
	 * @param inequal All specific values that the variable cannot take (have to be less than <strong>less</strong> and
	 *                greater than <strong>greater</strong>),
	 * @param less    The value that the variable has to be smaller than (has to be strictly greater than
	 *                <strong>less</strong>)
	 * @param greater The value that the variable has to be greater than
	 */
	public IntegerRestriction(final HashSet<Integer> inequal, final int less, final int greater) {
		super(inequal, less, greater);
		assert less > greater + 1;

		mValueCount = (less - greater - 1) - inequal.size();
		assert mValueCount > 0;
	}

	public Integer getValueCount() {
		return mValueCount;
	}

	public int getLess() {
		return mLess;
	}

	@Override
	public String toCode() {
		return "new " + this.getClass().getSimpleName() + "(Util.toHashSet("
				+ String.join(", ", Util.map(mInequal, (inequal) -> {
					return inequal.toString();
				}, new ArrayList<>())) + "), " + mLess + ", " + mGreater + ")";
	}
}