package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence;

import java.math.BigInteger;
import java.util.Collection;
import java.util.Collections;
import java.util.function.BiPredicate;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValue;

/**
 * Representation of a congruence value in the congruence domain
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */

public final class CongruenceDomainValue
		implements Comparable<CongruenceDomainValue>, INonrelationalValue<CongruenceDomainValue> {

	private BigInteger mValue;
	private boolean mIsBottom;
	private boolean mIsConstant;
	private boolean mNonZero;

	/**
	 * Creates a bottom value (shouldn't be called, just necessary for the static create-methods)
	 */
	private CongruenceDomainValue() {
		mValue = null;
		mIsBottom = true;
		mIsConstant = false;
		mNonZero = false;
	}

	protected static CongruenceDomainValue createTop() {
		return createNonConstant(BigInteger.ONE);
	}

	protected static CongruenceDomainValue createBottom() {
		return new CongruenceDomainValue();
	}

	protected static CongruenceDomainValue createNonConstant(final BigInteger value, final boolean nonZero) {
		if (value.signum() == 0) {
			return nonZero ? createBottom() : createConstant(BigInteger.ZERO);
		}
		final CongruenceDomainValue res = new CongruenceDomainValue();
		res.mValue = value.abs();
		res.mNonZero = nonZero;
		res.mIsBottom = false;
		return res;
	}

	protected static CongruenceDomainValue createNonConstant(final BigInteger value) {
		return createNonConstant(value, false);
	}

	protected static CongruenceDomainValue createConstant(final BigInteger value) {
		final CongruenceDomainValue res = new CongruenceDomainValue();
		res.mValue = value;
		res.mNonZero = value.signum() != 0;
		res.mIsBottom = false;
		res.mIsConstant = true;
		return res;
	}

	@Override
	public boolean isBottom() {
		return mIsBottom;
	}

	@Override
	public boolean isTop() {
		return !mIsBottom && !mNonZero && !mIsConstant && mValue.equals(BigInteger.ONE);
	}

	protected BigInteger value() {
		return mValue;
	}

	protected boolean isConstant() {
		return mIsConstant;
	}

	@Override
	public int compareTo(final CongruenceDomainValue other) {
		throw new UnsupportedOperationException(
				"The compareTo operation is not defined on congruence clases and can therefore not be used.");
	}

	@Override
	public CongruenceDomainValue merge(final CongruenceDomainValue other) {
		if (other == null) {
			return createBottom();
		}
		if (mIsBottom) {
			return other.copy();
		}
		if (other.mIsBottom) {
			return copy();
		}
		// If both are constant and have the same value, the result is also constant (otherwise not)
		if (mValue.equals(other.mValue) && mIsConstant && other.mIsConstant) {
			return copy();
		}
		return createNonConstant(mValue.gcd(other.mValue), mNonZero && other.mNonZero);
	}

	@Override
	public CongruenceDomainValue intersect(final CongruenceDomainValue other) {
		if (other == null || mIsBottom || other.mIsBottom) {
			return createBottom();
		}
		// If both are constant, return the value if it's the same, bottom otherwise
		if (mIsConstant && other.mIsConstant) {
			if (mValue.equals(other.mValue)) {
				return copy();
			}
			return createBottom();
		}
		// If one is constant, return the value if it's inside the other, bottom otherwise
		if (mIsConstant) {
			if (other.mNonZero && mValue.signum() == 0) {
				return createBottom();
			}
			if (mValue.mod(other.mValue.abs()).signum() == 0) {
				return copy();
			}
			return createBottom();
		}
		if (other.mIsConstant) {
			if (mNonZero && other.mValue.signum() == 0) {
				return createBottom();
			}
			if (other.mValue.mod(mValue.abs()).signum() == 0) {
				return other.copy();
			}
			return createBottom();
		}
		// Return the LCM as new value
		// LCM(a, b) = abs(a * b) / GCD(a, b)
		return createNonConstant(mValue.multiply(other.mValue).divide(mValue.gcd(other.mValue)),
				mNonZero || other.mNonZero);
	}

	@Override
	public CongruenceDomainValue add(final CongruenceDomainValue other) {
		if (other == null || mIsBottom || other.mIsBottom) {
			return createBottom();
		}
		if (mValue.signum() == 0) {
			return other.copy();
		}
		if (other.mValue.signum() == 0) {
			return copy();
		}
		if (mIsConstant && other.mIsConstant) {
			return createConstant(mValue.add(other.mValue));
		}
		boolean nonZero = false;
		if (mIsConstant) {
			nonZero = mValue.mod(other.mValue).signum() != 0;
		}
		if (other.mIsConstant) {
			nonZero = other.mValue.mod(mValue).signum() != 0;
		}
		return createNonConstant(mValue.gcd(other.mValue), nonZero);
	}

	@Override
	public CongruenceDomainValue subtract(final CongruenceDomainValue other) {
		if (other == null || mIsBottom || other.mIsBottom) {
			return createBottom();
		}
		if (mValue.signum() == 0) {
			return other.negate();
		}
		if (other.mValue.signum() == 0) {
			return copy();
		}
		if (mIsConstant && other.mIsConstant) {
			return createConstant(mValue.subtract(other.mValue));
		}
		boolean nonZero = false;
		if (mIsConstant) {
			nonZero = mValue.mod(other.mValue).signum() != 0;
		}
		if (other.mIsConstant) {
			nonZero = other.mValue.mod(mValue).signum() != 0;
		}
		return createNonConstant(mValue.gcd(other.mValue), nonZero);
	}

	protected CongruenceDomainValue mod(final CongruenceDomainValue other) {
		if (other == null || mIsBottom || other.mIsBottom) {
			return createBottom();
		}
		if (!other.mNonZero) {
			return createTop();
		}
		// If both are constant, simply calculate the result
		if (mIsConstant && other.mIsConstant) {
			return createConstant(mValue.mod(other.mValue.abs()));
		}
		// a % bZ = a if a >= 0 and a < b
		if (mIsConstant && mValue.signum() >= 0 && mValue.compareTo(other.mValue) < 0) {
			return createConstant(mValue);
		}
		// aZ % b = 0 if a % b = 0
		if (other.mIsConstant && mValue.mod(other.mValue.abs()).signum() == 0) {
			return createConstant(BigInteger.ZERO);
		}
		return createNonConstant(mValue.gcd(other.mValue), mIsConstant && mValue.mod(other.mValue).signum() != 0);
	}

	@Override
	public CongruenceDomainValue multiply(final CongruenceDomainValue other) {
		if (other == null || mIsBottom || other.mIsBottom) {
			return createBottom();
		}
		if (mIsConstant && other.mIsConstant) {
			return createConstant(mValue.multiply(other.mValue));
		}
		return createNonConstant(mValue.multiply(other.mValue), mNonZero && other.mNonZero);
	}

	@Override
	public CongruenceDomainValue divideReal(final CongruenceDomainValue other) {
		if (other == null || mIsBottom || other.mIsBottom) {
			return createBottom();
		}
		if (!other.mNonZero) {
			return createTop();
		}
		if (other.mIsConstant) {
			// If "real" result of the division is an integer, just calculate the result
			if (mValue.mod(other.mValue.abs()).signum() == 0) {
				if (mIsConstant) {
					return createConstant(mValue.divide(other.mValue));
				}
				return createNonConstant(mValue.divide(other.mValue), mNonZero);
			}
			if (mIsConstant) {
				BigInteger val = mValue.divide(other.mValue);
				// If a < 0, a / b doesn't give the expected result (euclidian divsion)
				if (mValue.signum() < 0) {
					if (other.mValue.signum() > 0) {
						val = val.subtract(BigInteger.ONE);
					} else {
						val = val.add(BigInteger.ONE);
					}
				}
				return createConstant(val);
			}
		}
		// If 0 < a < b: a / bZ = 0
		if (mIsConstant && mValue.signum() > 0 && mValue.compareTo(other.mValue) < 0) {
			return createConstant(BigInteger.ZERO);
		}
		// aZ \ {0} / b = 1Z \ {0} if a >= |b| (division can't be zero then)
		if (other.mIsConstant && mNonZero && mValue.compareTo(other.mValue.abs()) >= 0) {
			return createNonConstant(BigInteger.ONE, true);
		}
		return createTop();
	}

	@Override
	public CongruenceDomainValue negate() {
		if (mIsBottom) {
			return createBottom();
		}
		if (mIsConstant) {
			return createConstant(mValue.negate());
		}
		return copy();
	}

	@Override
	public String toString() {
		if (mIsBottom) {
			return "{}";
		}
		if (mIsConstant) {
			return mValue.toString();
		}
		if (mNonZero) {
			return mValue.toString() + "Z \\ {0}";
		}
		return mValue.toString() + "Z";

	}

	@Override
	public Term getTerm(final Script script, final Sort sort, final Term var) {
		assert sort.isNumericSort();
		if (mIsBottom) {
			return script.term("false");
		}
		if (mIsConstant) {
			return script.term("=", var, SmtUtils.constructIntValue(script, mValue));
		}
		final Term nonZeroTerm = script.term("not", script.term("=", var, SmtUtils.constructIntValue(script, BigInteger.ZERO)));
		if (mValue.equals(BigInteger.ONE)) {
			if (mNonZero) {
				return nonZeroTerm;
			}
			return script.term("true");
		}
		final Term modTerm =
				script.term("=", script.term("mod", var, SmtUtils.constructIntValue(script, mValue)), SmtUtils.constructIntValue(script, BigInteger.ZERO));
		if (mNonZero) {
			return script.term("and", modTerm, nonZeroTerm);
		}
		return modTerm;

	}

	/**
	 * Returns <code>true</code> if and only if <code>this</code> is equal to <code>other</code>.
	 */
	@Override
	public boolean isAbstractionEqual(final CongruenceDomainValue other) {
		if (other == null) {
			return false;
		}
		if (mIsBottom && other.mIsBottom) {
			return true;
		}
		return mValue.equals(other.mValue) && mIsConstant == other.mIsConstant && mNonZero == other.mNonZero;
	}

	/**
	 * Return a copy of the value
	 */
	@Override
	public CongruenceDomainValue copy() {
		if (mIsBottom) {
			return createBottom();
		}
		if (mIsConstant) {
			return createConstant(mValue);
		}
		return createNonConstant(mValue, mNonZero);
	}

	/**
	 * Return the the new value for x for a "x % this == rest" - expression (soft-merge)
	 */
	protected CongruenceDomainValue modEquals(final CongruenceDomainValue rest) {
		if (mIsBottom || rest == null || rest.mIsBottom) {
			return createBottom();
		}
		if (!mNonZero) {
			return createTop();
		}
		// If the rest is < 0, return bottom
		if (rest.mValue.signum() < 0) {
			return createBottom();
		}
		// If the rest is >= |this|, return bottom if rest is constant, otherwise the non-constant value of this
		// (because rest has to be 0 then, since all other values are too big)
		if (mIsConstant && rest.mValue.compareTo(mValue.abs()) >= 0) {
			if (rest.mNonZero) {
				return createBottom();
			}
			return createNonConstant(mValue);
		}
		// Otherwise return the GCD (=non-constant merge)
		return createNonConstant(mValue.gcd(rest.mValue), rest.mNonZero);
	}

	/**
	 * Returns <code>true</code> if this is contained in other.
	 *
	 * @param other
	 *            The other value to check against.
	 * @return <code>true</code> if and only if the value of this is contained in the value of other, <code>false</code>
	 */
	@Override
	public boolean isContainedIn(final CongruenceDomainValue other) {
		if (mIsBottom) {
			return true;
		}
		if (other.mIsBottom) {
			return false;
		}
		if (other.mIsConstant) {
			return mIsConstant && mValue.equals(other.mValue);
		}
		if (!mNonZero && other.mNonZero) {
			return false;
		}
		return mValue.mod(other.mValue).signum() == 0;
	}

	protected CongruenceDomainValue getNonZeroValue() {
		if (mIsBottom || mValue.signum() == 0) {
			return createBottom();
		}
		if (mIsConstant) {
			return copy();
		}
		return createNonConstant(mValue, true);
	}

	@Override
	public CongruenceDomainValue divideInteger(final CongruenceDomainValue other) {
		return divideReal(other);
	}

	@Override
	public CongruenceDomainValue modulo(final CongruenceDomainValue other) {
		return mod(other);
	}

	@Override
	public CongruenceDomainValue greaterThan(final CongruenceDomainValue other) {
		return createTop();
	}

	@Override
	public BooleanValue isGreaterThan(final CongruenceDomainValue other) {
		return keepZeroInverseBooleanAssociative(other, (a, b) -> a.compareTo(b) > 0);
	}

	@Override
	public CongruenceDomainValue greaterOrEqual(final CongruenceDomainValue other) {
		return createTop();
	}

	@Override
	public BooleanValue isGreaterOrEqual(final CongruenceDomainValue other) {
		return keepZeroInverseBooleanAssociative(other, (a, b) -> a.compareTo(b) >= 0);
	}

	@Override
	public CongruenceDomainValue lessThan(final CongruenceDomainValue other) {
		return createTop();
	}

	@Override
	public BooleanValue isLessThan(final CongruenceDomainValue other) {
		return keepZeroInverseBooleanAssociative(other, (a, b) -> a.compareTo(b) < 0);
	}

	@Override
	public CongruenceDomainValue lessOrEqual(final CongruenceDomainValue other) {
		return createTop();
	}

	@Override
	public BooleanValue isLessOrEqual(final CongruenceDomainValue other) {
		return keepZeroInverseBooleanAssociative(other, (a, b) -> a.compareTo(b) <= 0);
	}

	@Override
	public CongruenceDomainValue inverseModulo(final CongruenceDomainValue referenceValue,
			final CongruenceDomainValue oldValue, final boolean isLeft) {
		// If mod is at one side of an equality, the left side of the mod expression
		// changes according to the other side of the equality
		if (isLeft) {
			return oldValue.intersect(modEquals(referenceValue));
		}
		return oldValue;
	}

	@Override
	public CongruenceDomainValue inverseEquality(final CongruenceDomainValue oldValue,
			final CongruenceDomainValue referenceValue) {
		return oldValue.intersect(this);
	}

	@Override
	public CongruenceDomainValue inverseLessOrEqual(final CongruenceDomainValue oldValue, final boolean isLeft) {
		return keepZeroInverseNonAssociative(oldValue, isLeft, a -> a.signum() < 0);
	}

	@Override
	public CongruenceDomainValue inverseLessThan(final CongruenceDomainValue oldValue, final boolean isLeft) {
		return keepZeroInverseNonAssociative(oldValue, isLeft, a -> a.signum() <= 0);
	}

	@Override
	public CongruenceDomainValue inverseGreaterOrEqual(final CongruenceDomainValue oldValue, final boolean isLeft) {
		return keepZeroInverseNonAssociative(oldValue, isLeft, a -> a.signum() > 0);
	}

	@Override
	public CongruenceDomainValue inverseGreaterThan(final CongruenceDomainValue oldValue, final boolean isLeft) {
		return keepZeroInverseNonAssociative(oldValue, isLeft, a -> a.signum() >= 0);
	}

	@Override
	public CongruenceDomainValue inverseNotEqual(final CongruenceDomainValue oldValue,
			final CongruenceDomainValue referenceValue) {
		return keepZeroInverseAssociative(oldValue, a -> a.signum() == 0);
	}

	private CongruenceDomainValue keepZeroInverseNonAssociative(final CongruenceDomainValue oldValue,
			final boolean isLeft, final Predicate<BigInteger> signumCheck) {
		if (isLeft && isConstant() && signumCheck.test(value())) {
			return oldValue.getNonZeroValue();
		}
		return oldValue;
	}

	private CongruenceDomainValue keepZeroInverseAssociative(final CongruenceDomainValue oldValue,
			final Predicate<BigInteger> signumCheck) {
		if (isConstant() && signumCheck.test(value())) {
			return oldValue.getNonZeroValue();
		}
		return oldValue;
	}

	private BooleanValue keepZeroInverseBooleanAssociative(final CongruenceDomainValue oldValue,
			final BiPredicate<BigInteger, BigInteger> comparison) {
		if (isConstant() && oldValue.isConstant()) {
			return BooleanValue.getBooleanValue(comparison.test(value(), oldValue.value()));
		}
		return BooleanValue.TOP;
	}

	@Override
	public boolean canHandleReals() {
		return true;
	}

	@Override
	public boolean canHandleModulo() {
		return true;
	}

	@Override
	public BooleanValue isEqual(final CongruenceDomainValue secondOther) {
		if (isConstant() && secondOther.isConstant()) {
			return BooleanValue.getBooleanValue(value().equals(secondOther.value()));
		}
		return BooleanValue.TOP;
	}

	@Override
	public BooleanValue isNotEqual(final CongruenceDomainValue secondOther) {
		if (isConstant() && secondOther.isConstant()) {
			return BooleanValue.getBooleanValue(!value().equals(secondOther.value()));
		}
		return BooleanValue.TOP;
	}

	@Override
	public Collection<CongruenceDomainValue> complement() {
		if (!isConstant() && mValue == BigInteger.ONE) {
			// its top
			return Collections.singleton(createBottom());
		}
		// all other cases are top
		return Collections.singleton(createTop());
	}

	@Override
	public Collection<CongruenceDomainValue> complementInteger() {
		// no difference
		return complement();
	}

}
