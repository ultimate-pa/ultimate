package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datastructures;

import java.math.BigInteger;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.ArithmeticUtils;

public class IntValue implements Value {
	private final BigInteger mValue;
	public static final IntValue ZERO = new IntValue(BigInteger.ZERO);
	public static final IntValue ONE = new IntValue(BigInteger.ONE);
	public static final IntValue TWO = new IntValue(BigInteger.TWO);

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
		return new IntValue(ArithmeticUtils.euclideanDiv(mValue, other.mValue));
	}

	public IntValue mod(final IntValue other) {
		return new IntValue(ArithmeticUtils.euclideanMod(mValue, other.mValue));
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
		return BoolValue.TRUE;
	}

	@Override
	public BigInteger getValue() {
		return mValue;
	}

	@Override
	public String toString() {
		return mValue.toString();
	}

	@Override
	public Map<Term, Term> toTerm(final Script script, final Term var) {
		return Map.of(var, SmtUtils.constructIntValue(script, mValue));
	}

	@Override
	public BoolValue equals(final Value other) {
		if (other instanceof final IntValue iv) {
			return new BoolValue(mValue.equals(iv.mValue));
		}
		return BoolValue.FALSE;
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