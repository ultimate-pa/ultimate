package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

import java.math.BigInteger;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class IntValue implements Value {
	private final BigInteger mValue;
	public final static IntValue ZERO = new IntValue(BigInteger.ZERO);
	public final static IntValue ONE = new IntValue(BigInteger.ONE);
	public final static IntValue TWO = new IntValue(BigInteger.TWO);

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
	public BoolValue distinct(final Value other) {
		if (other instanceof final IntValue iv) {
			return new BoolValue(!mValue.equals(iv.mValue));
		}
		return BoolValue.mTrue;
	}

	@Override
	public BigInteger getValue() {
		return mValue;
	}

	@Override
	public String toString() {
		return mValue.toString();
	}

	private static ValueToTermStorage cache = ValueToTermStorage.getInstance();

	@Override
	public Map<Term, Term> toTerm(final Script script, final Term var) {
		return Map.of(var, cache.getInteger(script, this));
	}

	@Override
	public BoolValue equals(final Value other) {
		if (other instanceof final IntValue iv) {
			return new BoolValue(mValue.equals(iv.mValue));
		}
		return BoolValue.mFalse;
	}

	@Override
	public boolean equals(final Object b) {
		if (b instanceof final IntValue iv) {
			return mValue.equals(iv.mValue);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return mValue.hashCode();
	}

	@Override
	public int compareTo(final Value b) {
		if (b instanceof final IntValue iv) {
			return mValue.compareTo(iv.mValue);
		}
		return this.getClass().getSimpleName().compareTo(b.getClass().getSimpleName());
	}
}