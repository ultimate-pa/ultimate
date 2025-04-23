package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.Rational;

public class IntValue implements Value {
	private final BigInteger mValue;

	public IntValue(final BigInteger value) {
		mValue = value;
	}

	public IntValue add(final IntValue other) {
		return new IntValue(mValue.add(other.mValue));
	}

	public IntValue multiply(final IntValue other) {
		return new IntValue(mValue.multiply(other.mValue));
	}

	public IntValue div(final IntValue other) {
		final BigInteger n = other.mValue;
		final Rational div = Rational.valueOf(mValue, n);
		if (n.compareTo(BigInteger.ZERO) > 0) {
			// n > 0, (div m n) = floor(m/n)
			return new IntValue(div.floor().numerator());
		}
		// n < 0, (div m n) = ceil(m/n)
		return new IntValue(div.ceil().numerator());
	}

	public IntValue mod(final IntValue other) {
		// i == ((i / j) * j) + (i % j)
		// i % j == i - ((i / j) * j)
		final BigInteger div = div(other).mValue;
		return new IntValue(mValue.subtract(div.multiply(other.mValue)));
	}

	public IntValue subtract(final IntValue other) {
		return new IntValue(mValue.subtract(other.mValue));
	}

	public IntValue negate() {
		return new IntValue(mValue.negate());
	}

	public IntValue abs() {
		return new IntValue(mValue.abs());
	}

	public BoolValue leq(final IntValue other) {
		return new BoolValue(mValue.compareTo(other.mValue) <= 0);
	}

	public BoolValue lss(final IntValue other) {
		return new BoolValue(mValue.compareTo(other.mValue) < 0);
	}

	public BoolValue geq(final IntValue other) {
		return new BoolValue(mValue.compareTo(other.mValue) >= 0);
	}

	public BoolValue gtr(final IntValue other) {
		return new BoolValue(mValue.compareTo(other.mValue) > 0);
	}

	@Override
	public BoolValue equals(final Value other) {
		if (other instanceof final IntValue iv) {
			return new BoolValue(mValue.equals(iv.mValue));
		}
		return new BoolValue(false);
	}

	@Override
	public BoolValue distinct(final Value other) {
		if (other instanceof final IntValue iv) {
			return new BoolValue(!mValue.equals(iv.mValue));
		}
		return new BoolValue(true);
	}

	@Override
	public BigInteger getValue() {
		return mValue;
	}

	@Override
	public String toString() {
		return mValue.toString();
	}
}