package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Representation of a congruence value in the congruence domain
 * 
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */

public class CongruenceDomainValue implements Comparable<CongruenceDomainValue>{

	private BigInteger mValue;
	private boolean mIsBottom;
	private boolean mIsConstant;
	
	protected CongruenceDomainValue() {
		this(false);
	}

	protected CongruenceDomainValue(boolean isBottom) {
		mIsConstant = false;
		if (isBottom) {
			mValue = null;
			mIsBottom = true;
		} else {
			mValue = BigInteger.ONE;
			mIsBottom = false;
		}
	}
	
	protected CongruenceDomainValue(BigInteger value, boolean isConstant) {
		mIsBottom = false;
		mIsConstant = isConstant;
		if (value.equals(BigInteger.ZERO)) {
			mIsConstant = true;
		}
		mValue = mIsConstant ? value : value.abs();
	}
	
	protected CongruenceDomainValue(BigInteger value) {
		this(value, false);
	}
	
	protected boolean isBottom() {
		return mIsBottom;
	}
	
	protected BigInteger value() {
		return mValue;
	}
	
	protected boolean isConstant() {
		return mIsConstant;
	}
	
	@Override
	public int compareTo(CongruenceDomainValue other) {
		throw new UnsupportedOperationException(
		        "The compareTo operation is not defined on congruence clases and can therefore not be used.");
	}
	
	protected CongruenceDomainValue merge(CongruenceDomainValue other) {
		if (other == null) {
			return new CongruenceDomainValue(true);
		}
		if (mIsBottom) {
			return other.copy();
		}
		if (other.mIsBottom) {
			return copy();
		}
		// If both are constant and have the same value, the result is also constant (otherwise not)
		if (mValue.equals(other.mValue) && mIsConstant && other.mIsConstant) {
			return new CongruenceDomainValue(mValue, true);
		}
		return new CongruenceDomainValue(mValue.gcd(other.mValue));
	}
	
	protected CongruenceDomainValue intersect(CongruenceDomainValue other) {
		if (other == null || mIsBottom || other.mIsBottom) {
			return new CongruenceDomainValue(true);
		}
		// If both are constant, return the value if it's the same, bottom otherwise
		if (mIsConstant && other.mIsConstant) {
			if (mValue.equals(other.mValue)) {
				return new CongruenceDomainValue(mValue, true);
			} else {
				return new CongruenceDomainValue(true);
			}
		}
		// If one is constant, return the value if it's inside the other, bottom otherwise
		if (mIsConstant) {
			if (mValue.mod(other.mValue.abs()).equals(BigInteger.ZERO)) {
				return new CongruenceDomainValue(mValue, true);
			} else {
				return new CongruenceDomainValue(true);
			}
		}
		if (other.mIsConstant) {
			if (other.mValue.mod(mValue.abs()).equals(BigInteger.ZERO)) {
				return new CongruenceDomainValue(other.mValue, true);
			} else {
				return new CongruenceDomainValue(true);
			}
		}
		// Return the LCM as new value
		// LCM(a, b) = abs(a * b) / GCD(a, b)
		return new CongruenceDomainValue(mValue.multiply(other.mValue).divide(mValue.gcd(other.mValue)));
	}

	protected CongruenceDomainValue add(CongruenceDomainValue other) {
		if (other == null || mIsBottom || other.mIsBottom) {
			return new CongruenceDomainValue(true);
		}
		if (mIsConstant && other.mIsConstant) {
			return new CongruenceDomainValue(mValue.add(other.mValue), true);
		}
		return new CongruenceDomainValue(mValue.gcd(other.mValue));
	}
	
	protected CongruenceDomainValue subtract(CongruenceDomainValue other) {
		if (other == null || mIsBottom || other.mIsBottom) {
			return new CongruenceDomainValue(true);
		}
		if (mIsConstant && other.mIsConstant) {
			return new CongruenceDomainValue(mValue.subtract(other.mValue), true);
		}
		return new CongruenceDomainValue(mValue.gcd(other.mValue));
	}
	
	protected CongruenceDomainValue mod(CongruenceDomainValue other) {
		if (other == null || mIsBottom || other.mIsBottom || other.mValue.equals(BigInteger.ZERO)) {
			return new CongruenceDomainValue(true);
		}
		// If both are constant, simply calculate the result
		if (mIsConstant && other.mIsConstant) {
			return new CongruenceDomainValue(mValue.mod(other.mValue.abs()), true);
		}
		// a % bZ = a if a >= 0 and a < b
		if (mIsConstant && mValue.signum() >= 0 && mValue.compareTo(other.mValue) < 0) {
			return new CongruenceDomainValue(mValue, true);
		}
		// aZ % b = 0 if a % b = 0
		if (other.mIsConstant && mValue.mod(other.mValue.abs()).equals(BigInteger.ZERO)) {
			return new CongruenceDomainValue(BigInteger.ZERO, true);
		}
		return new CongruenceDomainValue(mValue.gcd(other.mValue));
	}
	
	protected CongruenceDomainValue multiply(CongruenceDomainValue other) {
		if (other == null || mIsBottom || other.mIsBottom) {
			return new CongruenceDomainValue(true);
		}
		return new CongruenceDomainValue(mValue.multiply(other.mValue), mIsConstant && other.mIsConstant);
	}
	
	protected CongruenceDomainValue divide (CongruenceDomainValue other) {
		if (other == null || mIsBottom || other.mIsBottom || other.mValue.equals(BigInteger.ZERO)) {
			return new CongruenceDomainValue(true);
		}
		if (other.mIsConstant) {
			// If "real" result of the division is an integer, just calculate the result
			if (mValue.mod(other.mValue.abs()).equals(BigInteger.ZERO)) {
				return new CongruenceDomainValue(mValue.divide(other.mValue), mIsConstant);
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
				return new CongruenceDomainValue(val, true);
			}
		}
		// If 0 < a < b: a / bZ = 0 
		if (mIsConstant && mValue.signum() > 0 && mValue.compareTo(other.mValue) < 0) {
			return new CongruenceDomainValue(BigInteger.ZERO, true);
		}
		return new CongruenceDomainValue();
	}
	
	protected CongruenceDomainValue negate() {
		if (mIsBottom) {
			return new CongruenceDomainValue(true);
		}
		return new CongruenceDomainValue(mValue.negate(), mIsConstant);
	}
	
	@Override
	public String toString() {
		if (mIsBottom) {
			return "{}";
		}
		if (mIsConstant) {
			return mValue.toString();
		}
		return mValue.toString() + "Z";
	}

	protected Term getTerm(final Script script, final Sort sort, final Term var) {
		assert sort.isNumericSort();
		if (mIsBottom) {
			return script.term("false");
		} 
		if (mIsConstant) {
			return script.term("=", var, script.numeral(mValue));
		}
		if (mValue.equals(BigInteger.ONE)) {
			return script.term("true");
		}
		// Return var mod value = 0
		return script.term("=", script.term("mod", var, script.numeral(mValue)), script.numeral(BigInteger.ZERO));
	}
	
	/*
	 * Check if two values are equal
	 */
	protected boolean isEqualTo(CongruenceDomainValue other) {
		if (other == null) {
			return false;
		}
		if (mIsBottom && other.mIsBottom) {
			return true;
		}
		return mValue.equals(other.mValue) && mIsConstant == other.mIsConstant;
	}
	
	/*
	 * Return a copy of the value
	 */
	protected CongruenceDomainValue copy() {
		if (mIsBottom) {
			return new CongruenceDomainValue(true);
		}
		return new CongruenceDomainValue(mValue, mIsConstant);
	}

	/*
	 * Return the the new value for x for a "x % this == rest" - expression (soft-merge)
	 */
	protected CongruenceDomainValue modEquals(CongruenceDomainValue rest) {
		if (mIsBottom ||  rest == null || rest.mIsBottom) {
			return new CongruenceDomainValue(true);
		}
		// If the rest is < 0, return bottom
		if (rest.mValue.signum() < 0) {
			return new CongruenceDomainValue(true);
		}
		// If the rest is >= |this|, return bottom if rest is constant, otherwise the non-constant value of this
		// (because rest has to be 0 then, since all other values are too big)
		if (mIsConstant && rest.mValue.compareTo(mValue.abs()) >= 0) {
			if (rest.mIsConstant) {
				return new CongruenceDomainValue(true);
			} else {
				return new CongruenceDomainValue(mValue);
			}			
		}
		// Otherwise return the non-constant value of the merge
		CongruenceDomainValue val = merge(rest);
		return new CongruenceDomainValue(val.mValue);
	}
}
