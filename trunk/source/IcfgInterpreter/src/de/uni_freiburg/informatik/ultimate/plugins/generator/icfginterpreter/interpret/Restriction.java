package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.Set;

public abstract class Restriction<T> {
	protected final Set<T> mInequal;
	protected final T mMinimum;
	protected final T mMaximum;

	public static class EmptyRangeException extends AssertionError {
		private static final long serialVersionUID = 1L;
	}

	/**
	 * @param inequal  All specific values that the variable cannot take
	 * @param minimum  The smallest value a variable can take
	 * @param maximuum The biggest value a variable can take
	 */
	public Restriction(final Set<T> inequal, final T minimum, final T maximum) {

		mInequal = inequal;
		mMinimum = minimum;
		mMaximum = maximum;
	}

	public Set<T> getInequal() {
		return mInequal;
	}

	/**
	 * Combine two restrictions. Returns this if other is not a restriction of the same type.
	 *
	 * @param other
	 * @return
	 */
	public abstract Restriction<T> combine(Restriction<?> other);

	@Override
	public abstract String toString();
}
