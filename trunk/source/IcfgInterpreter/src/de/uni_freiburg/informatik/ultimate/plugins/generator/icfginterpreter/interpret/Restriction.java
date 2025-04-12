package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.HashSet;

public abstract class Restriction<T> {
	protected final HashSet<T> mInequal;
	protected final T mMinimum;
	protected final T mMaximum;

	/**
	 * @param inequal  All specific values that the variable cannot take
	 * @param minimum  The smallest value a variable can take
	 * @param maximuum The biggest value a variable can take
	 */
	public Restriction(final HashSet<T> inequal, final T minimum, final T maximum) {
		mInequal = inequal;
		mMinimum = minimum;
		mMaximum = maximum;
	}

	public HashSet<T> getInequal() {
		return mInequal;
	}

	public abstract String toCode();

	@Override
	public abstract String toString();
}
