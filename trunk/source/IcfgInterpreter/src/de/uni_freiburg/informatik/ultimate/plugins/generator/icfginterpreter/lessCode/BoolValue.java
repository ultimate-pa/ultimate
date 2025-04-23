package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

public class BoolValue implements Value {
	private final Boolean mValue;

	public BoolValue(final Boolean value) {
		mValue = value;
	}

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
	public BoolValue equals(final Value other) {
		if (other instanceof final BoolValue bv) {
			return new BoolValue(mValue == bv.mValue);
		}
		return new BoolValue(false);
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
}