package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

public class Restriction<T> {
	private final T[] mInequal;
	private final T mLess;
	private final T mLessEqual;
	private final T mGreater;
	private final T mGreaterEqual;

	public Restriction(final T[] inequal, final T less, final T lessEqual, final T greaterEqual, final T greater) {
		mInequal = inequal;
		mLess = less;
		mLessEqual = lessEqual;
		mGreater = greater;
		mGreaterEqual = greaterEqual;
	}

}
