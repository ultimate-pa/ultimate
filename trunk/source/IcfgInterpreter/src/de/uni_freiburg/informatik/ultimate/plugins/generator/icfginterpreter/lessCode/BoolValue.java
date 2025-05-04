package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class BoolValue implements Value {
	private final Boolean mValue;

	public BoolValue(final Boolean value) {
		mValue = value;
	}

	public final static BoolValue mTrue = new BoolValue(true);
	public final static BoolValue mFalse = new BoolValue(false);

	public BoolValue not() {
		return new BoolValue(!mValue);
	}

	public BoolValue implies(final BoolValue other) {
		return new BoolValue(!mValue || other.mValue);
	}

	public BoolValue and(final BoolValue other) {
		return new BoolValue(mValue && other.mValue);
	}

	public BoolValue or(final BoolValue other) {
		return new BoolValue(mValue || other.mValue);
	}

	public BoolValue xor(final BoolValue other) {
		return new BoolValue(mValue ^ other.mValue);
	}

	@Override
	public BoolValue distinct(final Value other) {
		if (other instanceof final BoolValue bv) {
			return new BoolValue(mValue != bv.mValue);
		}
		return new BoolValue(true);
	}

	@Override
	public Boolean getValue() {
		return mValue;
	}

	@Override
	public String toString() {
		return mValue.toString();
	}

	@Override
	public Term toTerm(final Script script) {
		return script.getTheory().constant(mValue, script.getTheory().getBooleanSort());
	}

	@Override
	public BoolValue equals(final Value other) {
		if (other instanceof final BoolValue bv) {
			return new BoolValue(mValue == bv.mValue);
		}
		return new BoolValue(false);
	}

	@Override
	public boolean equals(final Object b) {
		if (b instanceof final BoolValue bv) {
			return mValue.equals(bv.mValue);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return mValue.hashCode();
	}

	@Override
	public int compareTo(final Value b) {
		if (b instanceof final BoolValue bv) {
			return mValue.compareTo(bv.mValue);
		}
		return this.getClass().getSimpleName().compareTo(b.getClass().getSimpleName());
	}
}