package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import org.apache.commons.math3.fraction.BigFraction;
import org.apache.commons.math3.fraction.BigFractionField;
import org.apache.commons.math3.linear.FieldVector;
import org.apache.commons.math3.linear.SparseFieldVector;

import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * Class that represents a vector with entries of type Rational. This is
 * archived by wrapping FieldVector<BigFraction>. BigFraction like Rational
 * utilizes BigInteger for its denominator and numerator so no precision is
 * lost. Further the sparse version SparseFieldVector<BigFraction> is used, so
 * only the non-zero entries are stored.
 */
public class RationalVector {
	/**
	 * Converts a Rational to a BigFraction.
	 */
	public static BigFraction getBigFractionFromRational(final Rational rational) {
		return new BigFraction(rational.numerator(), rational.denominator());
	}

	/**
	 * Converts a BigFraction to a Rational.
	 */
	public static Rational getRationalFromBigFraction(final BigFraction bigFraction) {
		return Rational.valueOf(bigFraction.getNumerator(), bigFraction.getDenominator());
	}

	/**
	 * Returns a vector with value 1 at index i and zero everywhere else.
	 */
	public static RationalVector getUnitVector(final int i, final int vectorLength) {
		final FieldVector<BigFraction> vector = new SparseFieldVector<>(BigFractionField.getInstance(), vectorLength);
		vector.setEntry(i, BigFraction.ONE);
		return new RationalVector(vector);
	}

	private final FieldVector<BigFraction> mVector;
	private Integer mFirstPivot = null;
	private Integer mLastPivot = null;

	RationalVector(final FieldVector<BigFraction> vector) {
		mVector = vector;
	}

	public RationalVector(final List<Rational> rationalList) {
		final FieldVector<BigFraction> vector = new SparseFieldVector<>(BigFractionField.getInstance(),
				rationalList.size());
		for (int i = 0; i < rationalList.size(); i++) {
			vector.setEntry(i, getBigFractionFromRational(rationalList.get(i)));
		}
		mVector = vector;
	}

	public static RationalVector fromIntList(final List<Integer> integerList) {
		final List<Rational> rationalList = new ArrayList<>();
		for (final Integer i : integerList) {
			rationalList.add(Rational.valueOf(i.longValue(), 1));
		}
		return new RationalVector(rationalList);
	}

	public FieldVector<BigFraction> getVector() {
		return mVector;
	}

	public int getLength() {
		return mVector.getDimension();
	}

	public Rational get(final int i) {
		final BigFraction entry = mVector.getEntry(i);
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

	/**
	 * Returns the first index with a non-zero entry.
	 */
	public int firstPivot() {
		if (mFirstPivot != null) {
			return mFirstPivot;
		}

		final int k = getLength();

		for (int i = 0; i < k; i++) {
			if (!get(i).equals(Rational.ZERO)) {
				mFirstPivot = i;
				return i;
			}
		}
		mFirstPivot = k;
		return k;
	}

	/**
	 * Returns the last index with a non-zero entry.
	 */
	public int lastPivot() {
		if (mLastPivot != null) {
			return mLastPivot;
		}

		final int k = getLength();

		for (int i = k - 1; i >= 0; i--) {
			if (!get(i).equals(Rational.ZERO)) {
				mLastPivot = i;
				return i;
			}
		}
		mLastPivot = -1;
		return -1;
	}

	@Override
	public int hashCode() {
		return Objects.hash(mVector);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final RationalVector other = (RationalVector) obj;
		return Objects.equals(mVector, other.mVector);
	}

	@Override
	public String toString() {
		return asList().toString();
	}

}
