package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.math.BigInteger;
import java.util.ArrayList;
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

	public static RationalVector getUnitVector(final int i, final int vectorLength) {
		final FieldVector<BigFraction> vector = new ArrayFieldVector<>(BigFractionField.getInstance(), vectorLength);
		vector.setEntry(i, BigFraction.ONE);
		return new RationalVector(vector);
	}

	private final FieldVector<BigFraction> mVector;

	RationalVector(final FieldVector<BigFraction> vector) {
		mVector = vector;
	}

	public RationalVector(final List<Rational> rationalList) {
		final ArrayFieldVector<BigFraction> vector = new ArrayFieldVector<>(BigFractionField.getInstance(),
				rationalList.size());
		for (int i = 0; i < rationalList.size(); i++) {
			vector.setEntry(i, getBigFractionFromRational(rationalList.get(i)));
		}
		mVector = vector;

	}

	public FieldVector<BigFraction> getVector() {
		return mVector;
	}

	public int getLength() {
		return mVector.getDimension();
	}

	public Rational get(final int column) {
		final BigFraction entry = mVector.getEntry(column);
		return RationalVector.getRationalFromBigFraction(entry);
	}

	public List<Rational> asList() {
		final List<Rational> list = new ArrayList<>();
		for (final BigFraction fraction : mVector.toArray()) {
			list.add(getRationalFromBigFraction(fraction));
		}
		return list;
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

	public RationalVector subtract(final RationalVector other) {
		return new RationalVector(mVector.subtract(other.getVector()));
	}

	public RationalVector negate() {
		return multiply(BigInteger.ONE.negate());
	}

	public RationalVector divide(final BigInteger factor) {
		return divide(Rational.valueOf(factor, BigInteger.ONE));
	}

	public RationalVector divide(final Rational factor) {
		return new RationalVector(mVector.mapDivide(getBigFractionFromRational(factor)));
	}

	@Override
	public String toString() {
		return mVector.toString();
	}

}
