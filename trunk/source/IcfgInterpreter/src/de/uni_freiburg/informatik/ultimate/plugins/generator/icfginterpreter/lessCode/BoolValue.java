package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

import java.util.Map;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class BoolValue implements Value {
	private final Boolean mValue;

	public BoolValue(final Boolean value) {
		mValue = value;
	}

	public static final BoolValue TRUE = new BoolValue(true);
	public static final BoolValue FALSE = new BoolValue(false);

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
			return new BoolValue(!Objects.equals(mValue, bv.mValue));
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
	public Map<Term, Term> toTerm(final Script script, final Term var) {
		return Map.of(var, mValue ? script.getTheory().mTrue : script.getTheory().mFalse);
	}

	@Override
	public BoolValue equals(final Value other) {
		if (other instanceof final BoolValue bv) {
			return new BoolValue(Objects.equals(mValue, bv.mValue));
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