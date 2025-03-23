package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.HashSet;

public class Restriction<T> {
	private final HashSet<T> mInequal;
	protected final T mLess;
	protected final T mGreater;

	/**
	 * @param inequal All specific values that the variable cannot take
	 * @param less    The value that the variable has to be smaller than
	 * @param greater The value that the variable has to be greater than
	 */
	public Restriction(final HashSet<T> inequal, final T less, final T greater) {
		mInequal = inequal;
		mLess = less;
		mGreater = greater;
	}

	public HashSet<T> getInequal() {
		return mInequal;
	}
}
