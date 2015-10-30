/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.intervaldomain;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

import java.math.BigInteger;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IAbstractValueFactory;

/**
 * @author Christopher Dillo
 *
 */
public class IntervalValue implements IAbstractValue<Interval> {
	/**
	 * The actual value of this
	 */
	private Interval mValue;

	/**
	 * The factory for creating values like this
	 */
	private IntervalValueFactory mFactory;

	/**
	 * The logger is needed in the operations
	 */
	private Logger mLogger;

	/**
	 * Constructor
	 * 
	 * @param value
	 * @param factory
	 * @param logger
	 */
	protected IntervalValue(Interval value, IntervalValueFactory factory, Logger logger) {
		mValue = value;
		mFactory = factory;
		mLogger = logger;
	}

	@Override
	public Interval getValue() {
		return mValue;
	}

	@Override
	public IAbstractValueFactory<?> getFactory() {
		return mFactory;
	}

	@Override
	public boolean isTrue() {
		return mValue.equals(Rational.ONE);
	}

	@Override
	public boolean isFalse() {
		assert (!isBottom()); // this should not be asked if bottom
		// 1 means true, everything else means false
		return (mValue.getUpperBound().compareTo(Rational.ONE) < 0)
				|| (mValue.getLowerBound().compareTo(Rational.ONE) > 0);
	}

	@Override
	public boolean isTop() {
		return (mValue.getLowerBound().compareTo(Rational.NEGATIVE_INFINITY) <= 0)
				&& (mValue.getUpperBound().compareTo(Rational.POSITIVE_INFINITY) >= 0);
	}

	@Override
	public boolean isBottom() {
		return mValue.isEmpty();
	}

	@Override
	public boolean representsSingleConcreteValue() {
		return mValue.isSingleValueInterval();
	}

	@Override
	public boolean isEqual(IAbstractValue<?> value) {
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null)
			return false;

		return (mValue.isEqual(intVal.getValue()));
	}

	@Override
	public boolean isSuperOrEqual(IAbstractValue<?> value) {
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null)
			return false;
		Interval interval = intVal.getValue();

		if (mValue.isEmpty())
			return interval.isEmpty();

		boolean lowerIsLessEq, upperIsGreaterEq;

		lowerIsLessEq = mValue.getLowerBound().compareTo(interval.getLowerBound()) <= 0;

		upperIsGreaterEq = mValue.getUpperBound().compareTo(interval.getUpperBound()) >= 0;

		return lowerIsLessEq && upperIsGreaterEq;
	}

	@Override
	public boolean isSub(IAbstractValue<?> value) {
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null)
			return false;
		Interval interval = intVal.getValue();

		if (mValue.isEmpty())
			return true;

		boolean lowerIsGreaterEq, upperIsLessEq;

		lowerIsGreaterEq = mValue.getLowerBound().compareTo(interval.getLowerBound()) >= 0;

		upperIsLessEq = mValue.getUpperBound().compareTo(interval.getUpperBound()) <= 0;

		return lowerIsGreaterEq && upperIsLessEq;
	}

	@Override
	public IntervalValue copy() {
		return mFactory.makeValue(mValue.copy());
	}

	@Override
	public IntervalValue add(IAbstractValue<?> value) {
		/*
		 * [a, b] + [x, y] = [a + x, b + y]
		 */
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null)
			return mFactory.makeBottomValue();
		Interval interval = intVal.getValue();

		if (mValue.isEmpty() || interval.isEmpty())
			return mFactory.makeBottomValue();

		Rational resultLower = mValue.getLowerBound().add(interval.getLowerBound());

		Rational resultUpper = mValue.getUpperBound().add(interval.getUpperBound());

		return mFactory.makeValue(new Interval(resultLower, resultUpper));
	}

	@Override
	public IntervalValue subtract(IAbstractValue<?> value) {
		/*
		 * [a, b] - [x, y] = [a - y, b - x]
		 */
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null)
			return mFactory.makeBottomValue();
		Interval interval = intVal.getValue();

		if (mValue.isEmpty() || interval.isEmpty())
			return mFactory.makeBottomValue();

		Rational resultLower = mValue.getLowerBound().sub(interval.getUpperBound());

		Rational resultUpper = mValue.getUpperBound().sub(interval.getLowerBound());

		return mFactory.makeValue(new Interval(resultLower, resultUpper));
	}

	@Override
	public IntervalValue multiply(IAbstractValue<?> value) {
		/*
		 * [a, b] * [x, y] = [min(a * x, a * y, b * x, b * y), max(a * x, a * y,
		 * b * x, b * y)] Optimisations by taking signs into account (and [a, b]
		 * * [x, y] = [x, y] * [a, b]): a >= 0, b >= 0, x >= 0, y >= 0 => [a *
		 * x, b * y] a >= 0, b >= 0, x <= 0, y >= 0 => [b * x, b * y] a >= 0, b
		 * >= 0, x <= 0, y <= 0 => [b * x, a * y] a <= 0, b >= 0, x <= 0, y >= 0
		 * => [min(a * y, b * x), max(a * x, b * y)] a <= 0, b >= 0, x <= 0, y
		 * <= 0 => [b * x, a * x] a <= 0, b <= 0, x <= 0, y <= 0 => [b * y, a *
		 * x]
		 */
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null)
			return mFactory.makeBottomValue();
		Interval interval = intVal.getValue();

		if (mValue.isEmpty() || interval.isEmpty())
			return mFactory.makeBottomValue();

		Rational resultLower, resultUpper;

		// rationals for calculations
		Rational l1 = mValue.getLowerBound();
		Rational u1 = mValue.getUpperBound();
		Rational l2 = interval.getLowerBound();
		Rational u2 = interval.getUpperBound();

		// flags for sign checks
		boolean l1_geq0 = l1.signum() >= 0;
		boolean u1_geq0 = u1.signum() >= 0;
		boolean l2_geq0 = l2.signum() >= 0;
		boolean u2_geq0 = u2.signum() >= 0;

		if (l1_geq0) {
			/*
			 * a >= 0, b >= 0, x >= 0, y >= 0 => [a * x, b * y] a >= 0, b >= 0,
			 * x <= 0, y >= 0 => [b * x, b * y] a >= 0, b >= 0, x <= 0, y <= 0
			 * => [b * x, a * y]
			 */
			if (l2_geq0) {
				/*
				 * a >= 0, b >= 0, x >= 0, y >= 0 => [a * x, b * y]
				 */
				resultLower = l1.mul(l2);
				resultUpper = u1.mul(u2);
			} else {
				/*
				 * a >= 0, b >= 0, x <= 0, y >= 0 => [b * x, b * y] a >= 0, b >=
				 * 0, x <= 0, y <= 0 => [b * x, a * y]
				 */
				resultLower = u1.mul(l2);
				if (u2_geq0) {
					/*
					 * a >= 0, b >= 0, x <= 0, y >= 0 => [b * x, b * y]
					 */
					resultUpper = u1.mul(u2);
				} else {
					/*
					 * a >= 0, b >= 0, x <= 0, y <= 0 => [b * x, a * y]
					 */
					resultUpper = l1.mul(u2);
				}
			}
		} else {
			/*
			 * a <= 0, b >= 0, x >= 0, y >= 0 => [a * y, b * y] a <= 0, b >= 0,
			 * x <= 0, y >= 0 => [min(a * y, b * x), max(a * x, b * y)] a <= 0,
			 * b >= 0, x <= 0, y <= 0 => [b * x, a * x] a <= 0, b <= 0, x >= 0,
			 * y >= 0 => [a * y, b * x] a <= 0, b <= 0, x <= 0, y >= 0 => [a *
			 * y, max(a * x, b * y)] a <= 0, b <= 0, x <= 0, y <= 0 => [b * y, a
			 * * x]
			 */
			if (u1_geq0) {
				/*
				 * a <= 0, b >= 0, x >= 0, y >= 0 => [a * y, b * y] a <= 0, b >=
				 * 0, x <= 0, y >= 0 => [min(a * y, b * x), max(a * x, b * y)] a
				 * <= 0, b >= 0, x <= 0, y <= 0 => [b * x, a * x]
				 */
				if (l2_geq0) {
					/*
					 * a <= 0, b >= 0, x >= 0, y >= 0 => [a * y, b * y]
					 */
					resultLower = l1.mul(u2);
					resultUpper = u1.mul(u2);
				} else {
					/*
					 * a <= 0, b >= 0, x <= 0, y >= 0 => [min(a * y, b * x),
					 * max(a * x, b * y)] a <= 0, b >= 0, x <= 0, y <= 0 => [b *
					 * x, a * x]
					 */
					if (u2_geq0) {
						/*
						 * a <= 0, b >= 0, x <= 0, y >= 0 => [min(a * y, b * x),
						 * max(a * x, b * y)]
						 */
						Rational l1u2 = l1.mul(u2);
						Rational u1l2 = u1.mul(l2);
						resultLower = ((l1u2.compareTo(u1l2) < 0) ? l1u2 : u1l2);
						Rational l1l2 = l1.mul(l2);
						Rational u1u2 = u1.mul(u2);
						resultUpper = ((l1l2.compareTo(u1u2) > 0) ? l1l2 : u1u2);
					} else {
						/*
						 * a <= 0, b >= 0, x <= 0, y <= 0 => [b * x, a * x]
						 */
						resultLower = u1.mul(l2);
						resultUpper = l1.mul(l2);
					}
				}
			} else {
				/*
				 * a <= 0, b <= 0, x >= 0, y >= 0 => [a * y, b * x] a <= 0, b <=
				 * 0, x <= 0, y >= 0 => [a * y, max(a * x, b * y)] a <= 0, b <=
				 * 0, x <= 0, y <= 0 => [b * y, a * x]
				 */
				if (l2_geq0) {
					/*
					 * a <= 0, b <= 0, x >= 0, y >= 0 => [a * y, b * x]
					 */
					resultLower = l1.mul(u2);
					resultUpper = u1.mul(l2);
				} else {
					/*
					 * a <= 0, b <= 0, x <= 0, y >= 0 => [a * y, max(a * x, b *
					 * y)] a <= 0, b <= 0, x <= 0, y <= 0 => [b * y, a * x]
					 */
					if (u2_geq0) {
						/*
						 * a <= 0, b <= 0, x <= 0, y >= 0 => [a * y, max(a * x,
						 * b * y)]
						 */
						resultLower = l1.mul(u2);

						Rational l1l2 = l1.mul(l2);
						Rational u1u2 = u1.mul(u2);
						resultUpper = ((l1l2.compareTo(u1u2) > 0) ? l1l2 : u1u2);
					} else {
						/*
						 * a <= 0, b <= 0, x <= 0, y <= 0 => [b * y, a * x]
						 */
						resultLower = u1.mul(u2);
						resultUpper = l1.mul(l2);
					}
				}
			}
		}

		if (resultLower.equals(Rational.NAN))
			resultLower = Rational.NEGATIVE_INFINITY;

		if (resultUpper.equals(Rational.NAN))
			resultUpper = Rational.POSITIVE_INFINITY;

		return mFactory.makeValue(new Interval(resultLower, resultUpper));
	}

	@Override
	public IntervalValue divide(IAbstractValue<?> value) {
		/*
		 * [a, b] / [x, y] = [min(a / x, a / y, b / x, b / y), max(a / x, a / y,
		 * b / x, b / y)] Important: Euclidean division!! Potential division by
		 * zero -> Warning/Error, value to (-infty, infty) ///// BOTTOM!!
		 * Optimisations by taking signs into account: a >= 0, b >= 0, x > 0, y
		 * > 0 => [a / y, b / x] a >= 0, b >= 0, x < 0, y < 0 => [b / y, a / x]
		 * a <= 0, b >= 0, x > 0, y > 0 => [a / x, b / x] a <= 0, b >= 0, x < 0,
		 * y < 0 => [b / y, a / y] a <= 0, b <= 0, x > 0, y > 0 => [a / x, b /
		 * y] a <= 0, b <= 0, x < 0, y < 0 => [b / x, a / y] x <= 0, y >= 0 =>
		 * (-infty, infty), Warning/Error
		 */
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null)
			return mFactory.makeBottomValue();
		Interval interval = intVal.getValue();

		if (mValue.isEmpty() || interval.isEmpty())
			return mFactory.makeBottomValue();
		Rational resultLower, resultUpper;

		// rationals for calculations
		Rational l1 = mValue.getLowerBound();
		Rational u1 = mValue.getUpperBound();
		Rational l2 = interval.getLowerBound();
		Rational u2 = interval.getUpperBound();

		// check for division by zero
		if ((l2.signum() <= 0) && (u2.signum() >= 0)) {
			mLogger.warn(String.format("Potential division by zero: %s / %s, returning TOP", mValue.toString(),
					interval.toString()));
			return mFactory.makeTopValue();
		}

		// flags for sign checks
		boolean l1_geq0 = l1.signum() >= 0;
		boolean u1_geq0 = u1.signum() >= 0;
		boolean lu2_g0 = l2.signum() > 0;

		// [a, a] / [x, x]
		if (mValue.isSingleValueInterval() && interval.isSingleValueInterval()) {
			Rational d = l1.div(l2);
			return mFactory.makeValue(new Interval(lu2_g0 ? d.floor() : d.ceil()));
		}

		if (l1_geq0) {
			/*
			 * a >= 0, b >= 0, x > 0, y > 0 => [a / y, b / x] a >= 0, b >= 0, x
			 * < 0, y < 0 => [b / y, a / x]
			 */
			if (lu2_g0) {
				/*
				 * a >= 0, b >= 0, x > 0, y > 0 => [a / y, b / x]
				 */
				resultLower = l1.div(u2).floor();
				resultUpper = u1.div(l2).floor();
			} else {
				/*
				 * a >= 0, b >= 0, x < 0, y < 0 => [b / y, a / x]
				 */
				resultLower = u1.div(u2).ceil();
				resultUpper = l1.div(l2).ceil();
			}
		} else {
			/*
			 * a <= 0, b >= 0, x > 0, y > 0 => [a / x, b / x] a <= 0, b >= 0, x
			 * < 0, y < 0 => [b / y, a / y] a <= 0, b <= 0, x > 0, y > 0 => [a /
			 * x, b / y] a <= 0, b <= 0, x < 0, y < 0 => [b / x, a / y]
			 */
			if (u1_geq0) {
				/*
				 * a <= 0, b >= 0, x > 0, y > 0 => [a / x, b / x] a <= 0, b >=
				 * 0, x < 0, y < 0 => [b / y, a / y]
				 */
				if (lu2_g0) {
					/*
					 * a <= 0, b >= 0, x > 0, y > 0 => [a / x, b / x]
					 */
					resultLower = l1.div(l2).floor();
					resultUpper = u1.div(l2).floor();
				} else {
					/*
					 * a <= 0, b >= 0, x < 0, y < 0 => [b / y, a / y]
					 */
					resultLower = u1.div(u2).ceil();
					resultUpper = l1.div(u2).ceil();
				}
			} else {
				/*
				 * a <= 0, b <= 0, x > 0, y > 0 => [a / x, b / y] a <= 0, b <=
				 * 0, x < 0, y < 0 => [b / x, a / y]
				 */
				if (lu2_g0) {
					/*
					 * a <= 0, b <= 0, x > 0, y > 0 => [a / x, b / y]
					 */
					resultLower = l1.div(l2).floor();
					resultUpper = u1.div(u2).floor();
				} else {
					/*
					 * a <= 0, b <= 0, x < 0, y < 0 => [b / x, a / y]
					 */
					resultLower = u1.div(l2).ceil();
					resultUpper = l1.div(u2).ceil();
				}
			}
		}

		if (resultLower.equals(Rational.NAN))
			resultLower = Rational.NEGATIVE_INFINITY;

		if (resultUpper.equals(Rational.NAN))
			resultUpper = Rational.POSITIVE_INFINITY;

		return mFactory.makeValue(new Interval(resultLower, resultUpper));
	}

	@Override
	public IntervalValue modulo(IAbstractValue<?> value) {
		/*
		 * [a, b] % [x, y] = [0, min(max(|a|, |b|), max(|x|, |y|)-1)]
		 */
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null)
			return mFactory.makeBottomValue();
		Interval interval = intVal.getValue();

		if (mValue.isEmpty() || interval.isEmpty())
			return mFactory.makeBottomValue();

		// [a, a] % [x, x]
		if (mValue.isSingleValueInterval() && interval.isSingleValueInterval()) {
			Rational a = mValue.getLowerBound();
			Rational x = interval.getLowerBound();

			if (x.compareTo(Rational.ZERO) == 0) {
				mLogger.error(
						String.format("Modulo division by zero: %s %% %s", mValue.toString(), interval.toString()));
				return mFactory.makeBottomValue();
			}

			BigInteger aInt = a.numerator().divide(a.denominator());

			BigInteger xInt = x.numerator().divide(x.denominator());

			BigInteger[] dr = aInt.divideAndRemainder(xInt);
			BigInteger r = dr[1].compareTo(BigInteger.ZERO) >= 0 ? dr[1] : xInt.abs().add(dr[1]);

			return mFactory.makeIntegerValue(r.toString());
		}

		// rationals for calculations
		Rational l1 = mValue.getLowerBound();
		Rational u1 = mValue.getUpperBound();
		Rational l2 = interval.getLowerBound();
		Rational u2 = interval.getUpperBound();

		// check for division by zero
		if ((l2.signum() <= 0) && (u2.signum() >= 0)) {
			mLogger.warn(String.format("Potential modulo division by zero: %s %% %s, returning [0, infty)",
					mValue.toString(), interval.toString()));
			return mFactory.makeValue(new Interval(Rational.ZERO, Rational.POSITIVE_INFINITY));
		}

		Rational max1 = l1.compareTo(u1) > 0 ? l1 : u1;

		Rational max2 = l2.compareTo(u2) > 0 ? l2 : u2;
		max2 = max2.sub(Rational.ONE);

		if (max1.compareTo(max2) < 0)
			return mFactory.makeValue(new Interval(Rational.ZERO, max1));

		return mFactory.makeValue(new Interval(Rational.ZERO, max2));
	}

	@Override
	public IntervalValue negative() {
		return mFactory.makeValue(new Interval(mValue.getUpperBound().negate(), mValue.getLowerBound().negate()));
	}

	@Override
	public IntervalValue compareIsEqual(IAbstractValue<?> value) {
		/*
		 * [a, b] == [x, y] => [max(a, x), min(b, y)]
		 */
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null)
			return mFactory.makeBottomValue();
		Interval interval = intVal.getValue();

		if (mValue.isEmpty() || interval.isEmpty())
			return mFactory.makeBottomValue();

		// rationals for calculations
		Rational l1 = mValue.getLowerBound();
		Rational u1 = mValue.getUpperBound();
		Rational l2 = interval.getLowerBound();
		Rational u2 = interval.getUpperBound();

		Rational resultLower = l1.compareTo(l2) > 0 ? l1 : l2;

		Rational resultUpper = u1.compareTo(u2) < 0 ? u1 : u2;

		return mFactory.makeValue(new Interval(resultLower, resultUpper));
	}

	@Override
	public IntervalValue compareIsNotEqual(IAbstractValue<?> value) {
		/*
		 * [a, b] != [x, y] => [min(a, x), max(b, y)] [a, a] != [a, a] => empty
		 * 
		 * // the following 4 cases are only valid for integers [a, a] != [a, y]
		 * => [a+1, y] [a, a] != [x, a] => [x, a-1] [a, y] != [a, a] => [a+1, y]
		 * [x, a] != [a, a] => [x, a-1]
		 */
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null) {
			return mFactory.makeBottomValue();
		}
		Interval interval = intVal.getValue();

		if (mValue.isEmpty() || interval.isEmpty()) {
			return mFactory.makeBottomValue();
		}

		// rationals for calculations
		Rational l1 = mValue.getLowerBound();
		Rational u1 = mValue.getUpperBound();
		Rational l2 = interval.getLowerBound();
		Rational u2 = interval.getUpperBound();

		// [a, a] != [a, a] => empty
		if (mValue.isSingleValueInterval()) {
			if (interval.isSingleValueInterval() && (l1.compareTo(l2) == 0)) {
				return mFactory.makeBottomValue();
			}

			// TODO: do the 4 integer cases (a flag for whether this is an
			// integer is needed)
			// if(l1.compareTo(l2) == 0)
			// {
			// return m_factory.makeValue(new Interval(l2.add(Rational.ONE),
			// u2));
			// }
		}

		Rational resultLower = l1.compareTo(l2) < 0 ? l1 : l2;

		Rational resultUpper = u1.compareTo(u2) > 0 ? u1 : u2;

		return mFactory.makeValue(new Interval(resultLower, resultUpper));
	}

	@Override
	public IntervalValue compareIsLess(IAbstractValue<?> value) {
		/*
		 * [a, b] < [x, y] => [a, min(b, y - 1)]
		 */
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null)
			return mFactory.makeBottomValue();
		Interval interval = intVal.getValue();

		if (mValue.isEmpty() || interval.isEmpty())
			return mFactory.makeBottomValue();

		// rationals for calculations
		Rational u1 = mValue.getUpperBound();
		Rational u2m1 = interval.getUpperBound().sub(Rational.ONE);

		Rational resultUpper = u1.compareTo(u2m1) < 0 ? u1 : u2m1;

		return mFactory.makeValue(new Interval(mValue.getLowerBound(), resultUpper));
	}

	@Override
	public IntervalValue compareIsGreater(IAbstractValue<?> value) {
		/*
		 * [a, b] > [x, y] => [max(a, x + 1), b]
		 */
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null)
			return mFactory.makeBottomValue();
		Interval interval = intVal.getValue();

		if (mValue.isEmpty() || interval.isEmpty())
			return mFactory.makeBottomValue();

		// rationals for calculations
		Rational l1 = mValue.getLowerBound();
		Rational l2p1 = interval.getLowerBound().add(Rational.ONE);

		Rational resultLower = l1.compareTo(l2p1) > 0 ? l1 : l2p1;

		return mFactory.makeValue(new Interval(resultLower, mValue.getUpperBound()));
	}

	@Override
	public IntervalValue compareIsLessEqual(IAbstractValue<?> value) {
		/*
		 * [a, b] <= [x, y] => [a, min(b, y)]
		 */
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null)
			return mFactory.makeBottomValue();
		Interval interval = intVal.getValue();

		if (mValue.isEmpty() || interval.isEmpty())
			return mFactory.makeBottomValue();

		// rationals for calculations
		Rational u1 = mValue.getUpperBound();
		Rational u2 = interval.getUpperBound();

		Rational resultUpper = u1.compareTo(u2) < 0 ? u1 : u2;

		return mFactory.makeValue(new Interval(mValue.getLowerBound(), resultUpper));
	}

	@Override
	public IntervalValue compareIsGreaterEqual(IAbstractValue<?> value) {
		/*
		 * [a, b] >= [x, y] => [max(a, x), b]
		 */
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null)
			return mFactory.makeBottomValue();
		Interval interval = intVal.getValue();

		if (mValue.isEmpty() || interval.isEmpty())
			return mFactory.makeBottomValue();

		// rationals for calculations
		Rational l1 = mValue.getLowerBound();
		Rational l2 = interval.getLowerBound();

		Rational resultLower = l1.compareTo(l2) > 0 ? l1 : l2;

		return mFactory.makeValue(new Interval(resultLower, mValue.getUpperBound()));
	}

	@Override
	public IntervalValue logicIff(IAbstractValue<?> value) {
		// return isBottom() && value.isBottom()
		// ? m_factory.makeBoolValue(true)
		// : m_factory.makeTopValue();

		return null;
	}

	@Override
	public IntervalValue logicImplies(IAbstractValue<?> value) {
		// A => B
		// return isBottom()
		// ? m_factory.makeBoolValue(true)
		// : m_factory.makeTopValue();
		return null;
	}

	@Override
	public IntervalValue logicAnd(IAbstractValue<?> value) {
		return null; // TODO: interpret int as boolean
	}

	@Override
	public IntervalValue logicOr(IAbstractValue<?> value) {
		return null; // TODO: interpret int as boolean
	}

	@Override
	public IntervalValue logicNot() {
		return null; // TODO: interpret int as boolean
	}

	@Override
	public IntervalValue bitVectorConcat(IAbstractValue<?> value) {
		return null;
	}

	@Override
	public IntervalValue bitVectorAccess(int start, int end) {
		return null;
	}

	/**
	 * Visualized as string
	 */
	public String toString() {
		return "Interval: " + mValue.toString();
	}

	@Override
	public Term getTerm(Script script, Term variable) {
		//TODO: Review this code by Fabian
		
		Term lowerBound = null;
		Term upperBound = null;
		Rational lower = getValue().getLowerBound();
		Rational upper = getValue().getUpperBound();
		if (lower.isRational() && upper.isRational()) {
			if (!lower.equals(upper)) {
				lowerBound = lower.toTerm(variable.getSort());
				lowerBound = script.term("<=", lowerBound, variable);
				upperBound = upper.toTerm(variable.getSort());
				upperBound = script.term(">=", upperBound, variable);
				return script.term("and", lowerBound, upperBound);
			} else {
				lowerBound = lower.toTerm(variable.getSort());
				return script.term("=", lowerBound, variable);
			}
		} else if ((lower == Rational.NEGATIVE_INFINITY) && (upper == Rational.POSITIVE_INFINITY)) {
			return script.term("true");
		} else if ((lower == Rational.NEGATIVE_INFINITY) && (upper.isRational())) {
			upperBound = upper.toTerm(variable.getSort());
			return script.term(">=", upperBound, variable);
		} else if ((lower.isRational()) && (upper == Rational.POSITIVE_INFINITY)) {
			lowerBound = lower.toTerm(variable.getSort());
			return script.term("<=", lowerBound, variable);
		} else {
			return script.term("false");
		}
	}
}
