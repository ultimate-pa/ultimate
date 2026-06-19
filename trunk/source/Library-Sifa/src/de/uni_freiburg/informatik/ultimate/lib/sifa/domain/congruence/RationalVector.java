package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.math.BigInteger;
import java.util.List;

import org.apache.commons.math3.fraction.BigFraction;
import org.apache.commons.math3.fraction.BigFractionField;
import org.apache.commons.math3.linear.ArrayFieldVector;
import org.apache.commons.math3.linear.FieldVector;

import de.uni_freiburg.informatik.ultimate.logic.Rational;

public class RationalVector {
	public static BigFraction getBigFractionFromRational(final Rational rational) {
		return new BigFraction(rational.numerator(), rational.denominator());
	}

	public static Rational getRationalFromBigFraction(final BigFraction bigFraction) {
		return Rational.valueOf(bigFraction.getNumerator(), bigFraction.getDenominator());
	}

	private final FieldVector<BigFraction> mVector;

	RationalVector(final FieldVector<BigFraction> vector) {
		mVector = vector;
	}

	public RationalVector(final List<Rational> rationalList) {
		mVector = new ArrayFieldVector<>(BigFractionField.getInstance(), rationalList.size());
	}

	public FieldVector<BigFraction> getVector() {
		return mVector;
	}

	public Rational get(final int column) {
		final BigFraction entry = mVector.getEntry(column);
		return RationalVector.getRationalFromBigFraction(entry);
	}

	public RationalVector multiply(final BigInteger factor) {
		return multiply(Rational.valueOf(factor, BigInteger.ONE));
	}

	public RationalVector multiply(final Rational factor) {
		return new RationalVector(mVector.mapMultiply(getBigFractionFromRational(factor)));
	}

	public RationalVector add(final RationalVector other) {
		return new RationalVector(mVector.add(other.getVector()));
	}

	@Override
	public String toString() {
		return mVector.toString();
	}
}
