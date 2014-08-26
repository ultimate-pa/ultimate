/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.intervaldomain;

import java.math.BigInteger;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain.SignValue;

/**
 * @author Christopher Dillo
 *
 */
public class IntervalValue implements IAbstractValue<Interval> {
	
	private Interval m_value;
	
	private IntervalDomainFactory m_factory;
	
	private Logger m_logger;
	
	protected IntervalValue(Interval value, IntervalDomainFactory factory, Logger logger) {
		m_value = value;
		m_factory = factory;
		m_logger = logger;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#getValue()
	 */
	@Override
	public Interval getValue() {
		return m_value;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#isTop()
	 */
	@Override
	public boolean isTop() {
		return (m_value.getLowerBound().compareTo(Rational.NEGATIVE_INFINITY) <= 0)
				&& (m_value.getUpperBound().compareTo(Rational.POSITIVE_INFINITY) >= 0);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#isBottom()
	 */
	@Override
	public boolean isBottom() {
		return m_value.isEmpty();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#representsSingleConcreteValue()
	 */
	@Override
	public boolean representsSingleConcreteValue() {
		return m_value.isSingleValueInterval();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#isEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean isEqual(IAbstractValue<?> value) {
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null) return false;
		
		return (m_value.isEqual(intVal.getValue()));
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#isSuper(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean isSuper(IAbstractValue<?> value) {
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null) return false;
		Interval interval = intVal.getValue();
		
		if (m_value.isEmpty())
			return interval.isEmpty();
		
		boolean lowerIsLessEq, upperIsGreaterEq;
		
		lowerIsLessEq = m_value.getLowerBound().compareTo(interval.getLowerBound()) <= 0;

		upperIsGreaterEq = m_value.getUpperBound().compareTo(interval.getUpperBound()) >= 0;
		
		return lowerIsLessEq && upperIsGreaterEq;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#isSub(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean isSub(IAbstractValue<?> value) {
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null) return false;
		Interval interval = intVal.getValue();
		
		if (m_value.isEmpty())
			return true;
		
		boolean lowerIsGreaterEq, upperIsLessEq;
		
		lowerIsGreaterEq = m_value.getLowerBound().compareTo(interval.getLowerBound()) >= 0;

		upperIsLessEq = m_value.getUpperBound().compareTo(interval.getUpperBound()) <= 0;
		
		return lowerIsGreaterEq && upperIsLessEq;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#copy()
	 */
	@Override
	public IntervalValue copy() {
		return m_factory.makeValue(m_value.copy());
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#add(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IntervalValue add(IAbstractValue<?> value) {
		/*
		 * [a, b] + [x, y] = [a + x, b + y]
		 */
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null) return m_factory.makeBottomValue();
		Interval interval = intVal.getValue();
		
		if (m_value.isEmpty() || interval.isEmpty())
			return m_factory.makeBottomValue();
		
		Rational resultLower = m_value.getLowerBound().add(interval.getLowerBound());
		
		Rational resultUpper = m_value.getUpperBound().add(interval.getUpperBound());
		
		return m_factory.makeValue(new Interval(resultLower, resultUpper));
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#subtract(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IntervalValue subtract(IAbstractValue<?> value) {
		/*
		 * [a, b] - [x, y] = [a - y, b - x]
		 */
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null) return m_factory.makeBottomValue();
		Interval interval = intVal.getValue();
		
		if (m_value.isEmpty() || interval.isEmpty())
			return m_factory.makeBottomValue();
		
		Rational resultLower = m_value.getLowerBound().sub(interval.getUpperBound());
		
		Rational resultUpper = m_value.getUpperBound().sub(interval.getLowerBound());
		
		return m_factory.makeValue(new Interval(resultLower, resultUpper));
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#multiply(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IntervalValue multiply(IAbstractValue<?> value) {
		/*
		 * [a, b] * [x, y] = [min(a * x, a * y, b * x, b * y),
		 * 					   max(a * x, a * y, b * x, b * y)]
		 * Optimisations by taking signs into account (and [a, b] * [x, y] = [x, y] * [a, b]):
		 * 		a >= 0, b >= 0, x >= 0, y >= 0 => [a * x, b * y]
		 * 		a >= 0, b >= 0, x <= 0, y >= 0 => [b * x, b * y]
		 * 		a >= 0, b >= 0, x <= 0, y <= 0 => [b * x, a * y]
		 * 		a <= 0, b >= 0, x <= 0, y >= 0 => [min(a * y, b * x), max(a * x, b * y)]
		 * 		a <= 0, b >= 0, x <= 0, y <= 0 => [b * x, a * x]
		 * 		a <= 0, b <= 0, x <= 0, y <= 0 => [b * y, a * x]
		 */
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null) return m_factory.makeBottomValue();
		Interval interval = intVal.getValue();
		
		if (m_value.isEmpty() || interval.isEmpty())
			return m_factory.makeBottomValue();

		Rational resultLower, resultUpper;

		// rationals for calculations
		Rational l1 = m_value.getLowerBound();
		Rational u1 = m_value.getUpperBound();
		Rational l2 = interval.getLowerBound();
		Rational u2 = interval.getUpperBound();

		// flags for sign checks
		boolean l1_geq0 = l1.signum() >= 0;
		boolean u1_geq0 = u1.signum() >= 0;
		boolean l2_geq0 = l2.signum() >= 0;
		boolean u2_geq0 = u2.signum() >= 0;
		
		if (l1_geq0) {
			/*
			 * 	a >= 0, b >= 0, x >= 0, y >= 0 => [a * x, b * y]
			 * 	a >= 0, b >= 0, x <= 0, y >= 0 => [b * x, b * y]
			 * 	a >= 0, b >= 0, x <= 0, y <= 0 => [b * x, a * y]
			 */
			if (l2_geq0) {
				/*
				 * 	a >= 0, b >= 0, x >= 0, y >= 0 => [a * x, b * y]
				 */
				resultLower = l1.mul(l2);
				resultUpper = u1.mul(u2);
			} else {
				/*
				 * 	a >= 0, b >= 0, x <= 0, y >= 0 => [b * x, b * y]
				 * 	a >= 0, b >= 0, x <= 0, y <= 0 => [b * x, a * y]
				 */
				resultLower = u1.mul(l2);
				if (u2_geq0) {
					/*
					 * 	a >= 0, b >= 0, x <= 0, y >= 0 => [b * x, b * y]
					 */
					resultUpper = u1.mul(u2);
				} else {
					/*
					 * 	a >= 0, b >= 0, x <= 0, y <= 0 => [b * x, a * y]
					 */
					resultUpper = l1.mul(u2);
				}
			}
		} else {
			/*
			 * 	a <= 0, b >= 0, x >= 0, y >= 0 => [a * y, b * y]
			 * 	a <= 0, b >= 0, x <= 0, y >= 0 => [min(a * y, b * x), max(a * x, b * y)]
			 * 	a <= 0, b >= 0, x <= 0, y <= 0 => [b * x, a * x]
			 * 	a <= 0, b <= 0, x >= 0, y >= 0 => [a * y, b * x]
			 * 	a <= 0, b <= 0, x <= 0, y >= 0 => [a * y, max(a * x, b * y)]
			 * 	a <= 0, b <= 0, x <= 0, y <= 0 => [b * y, a * x]
			 */
			if (u1_geq0) {
				/*
				 * 	a <= 0, b >= 0, x >= 0, y >= 0 => [a * y, b * y]
				 * 	a <= 0, b >= 0, x <= 0, y >= 0 => [min(a * y, b * x), max(a * x, b * y)]
				 * 	a <= 0, b >= 0, x <= 0, y <= 0 => [b * x, a * x]
				 */
				if (l2_geq0) {
					/*
					 * 	a <= 0, b >= 0, x >= 0, y >= 0 => [a * y, b * y]
					 */
					resultLower = l1.mul(u2);
					resultUpper = u1.mul(u2);
				} else {
					/*
					 * 	a <= 0, b >= 0, x <= 0, y >= 0 => [min(a * y, b * x), max(a * x, b * y)]
					 * 	a <= 0, b >= 0, x <= 0, y <= 0 => [b * x, a * x]
					 */
					if (u2_geq0) {
						/*
						 * 	a <= 0, b >= 0, x <= 0, y >= 0 => [min(a * y, b * x), max(a * x, b * y)]
						 */
						Rational l1u2 = l1.mul(u2);
						Rational u1l2 = u1.mul(l2);
						resultLower = ((l1u2.compareTo(u1l2) < 0) ? l1u2 : u1l2);
						Rational l1l2 = l1.mul(l2);
						Rational u1u2 = u1.mul(u2);
						resultUpper = ((l1l2.compareTo(u1u2) > 0) ? l1l2 : u1u2);
					} else {
						/*
						 * 	a <= 0, b >= 0, x <= 0, y <= 0 => [b * x, a * x]
						 */
						resultLower = u1.mul(l2);
						resultUpper = l1.mul(l2);
					}
				}
			} else {
				/*
				 * 	a <= 0, b <= 0, x >= 0, y >= 0 => [a * y, b * x]
				 * 	a <= 0, b <= 0, x <= 0, y >= 0 => [a * y, max(a * x, b * y)]
				 * 	a <= 0, b <= 0, x <= 0, y <= 0 => [b * y, a * x]
				 */
				if (l2_geq0) {
					/*
					 * 	a <= 0, b <= 0, x >= 0, y >= 0 => [a * y, b * x]
					 */
					resultLower = l1.mul(u2);
					resultUpper = u1.mul(l2);
				} else {
					/*
					 * 	a <= 0, b <= 0, x <= 0, y >= 0 => [a * y, max(a * x, b * y)]
					 * 	a <= 0, b <= 0, x <= 0, y <= 0 => [b * y, a * x]
					 */
					if (u2_geq0) {
						/*
						 * 	a <= 0, b <= 0, x <= 0, y >= 0 => [a * y, max(a * x, b * y)]
						 */
						resultLower = l1.mul(u2);

						Rational l1l2 = l1.mul(l2);
						Rational u1u2 = u1.mul(u2);
						resultUpper = ((l1l2.compareTo(u1u2) > 0) ? l1l2 : u1u2);
					} else {
						/*
						 * 	a <= 0, b <= 0, x <= 0, y <= 0 => [b * y, a * x]
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
		
		return m_factory.makeValue(new Interval(resultLower, resultUpper));
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#divide(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IntervalValue divide(IAbstractValue<?> value) {
		/*
		 * [a, b] / [x, y] = [min(a / x, a / y, b / x, b / y),
		 * 					max(a / x, a / y, b / x, b / y)]
		 * Important: Euclidean division!!
		 * Potential division by zero -> Warning/Error, value to (-infty, infty) ///// BOTTOM!!
		 * Optimisations by taking signs into account:
		 * 		a >= 0, b >= 0, x >  0, y >  0 => [a / y, b / x]
		 * 		a >= 0, b >= 0, x <  0, y <  0 => [b / y, a / x]
		 * 		a <= 0, b >= 0, x >  0, y >  0 => [a / x, b / x]
		 * 		a <= 0, b >= 0, x <  0, y <  0 => [b / y, a / y]
		 * 		a <= 0, b <= 0, x >  0, y >  0 => [a / x, b / y]
		 * 		a <= 0, b <= 0, x <  0, y <  0 => [b / x, a / y]
				                x <= 0, y >= 0 => (-infty, infty), Warning/Error
		 */
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null) return m_factory.makeBottomValue();
		Interval interval = intVal.getValue();
		
		if (m_value.isEmpty() || interval.isEmpty())
			return m_factory.makeBottomValue();
		Rational resultLower, resultUpper;

		// rationals for calculations
		Rational l1 = m_value.getLowerBound();
		Rational u1 = m_value.getUpperBound();
		Rational l2 = interval.getLowerBound();
		Rational u2 = interval.getUpperBound();
		
		// check for division by zero
		if ((l2.signum() <= 0) && (u2.signum() >= 0)) {
			m_logger.warn(String.format("Potential division by zero: %s / %s", m_value.toString(), interval.toString()));
			return m_factory.makeBottomValue();
		}

		// flags for sign checks
		boolean l1_geq0 = l1.signum() >= 0;
		boolean u1_geq0 = u1.signum() >= 0;
		boolean lu2_g0 = l2.signum() > 0;

		// [a, a] / [x, x]
		if (m_value.isSingleValueInterval() && interval.isSingleValueInterval()) {
			Rational d = l1.div(l2);
			return m_factory.makeValue(new Interval(lu2_g0 ? d.floor() : d.ceil()));
		}
		
		if (l1_geq0) {
			/*
			 * 		a >= 0, b >= 0, x >  0, y >  0 => [a / y, b / x]
			 * 		a >= 0, b >= 0, x <  0, y <  0 => [b / y, a / x]
			 */
			if (lu2_g0) {
				/*
				 * 		a >= 0, b >= 0, x >  0, y >  0 => [a / y, b / x]
				 */
				resultLower = l1.div(u2).floor();
				resultUpper = u1.div(l2).floor();
			} else {
				/*
				 * 		a >= 0, b >= 0, x <  0, y <  0 => [b / y, a / x]
				 */
				resultLower = u1.div(u2).ceil();
				resultUpper = l1.div(l2).ceil();
			}
		} else {
			/*
			 * 		a <= 0, b >= 0, x >  0, y >  0 => [a / x, b / x]
			 * 		a <= 0, b >= 0, x <  0, y <  0 => [b / y, a / y]
			 * 		a <= 0, b <= 0, x >  0, y >  0 => [a / x, b / y]
			 * 		a <= 0, b <= 0, x <  0, y <  0 => [b / x, a / y]
			 */
			if (u1_geq0) {
				/*
				 * 		a <= 0, b >= 0, x >  0, y >  0 => [a / x, b / x]
				 * 		a <= 0, b >= 0, x <  0, y <  0 => [b / y, a / y]
				 */
				if (lu2_g0) {
					/*
					 * 		a <= 0, b >= 0, x >  0, y >  0 => [a / x, b / x]
					 */
					resultLower = l1.div(l2).floor();
					resultUpper = u1.div(l2).floor();
				} else {
					/*
					 * 		a <= 0, b >= 0, x <  0, y <  0 => [b / y, a / y]
					 */
					resultLower = u1.div(u2).ceil();
					resultUpper = l1.div(u2).ceil();
				}
			} else {
				/*
				 * 		a <= 0, b <= 0, x >  0, y >  0 => [a / x, b / y]
				 * 		a <= 0, b <= 0, x <  0, y <  0 => [b / x, a / y]
				 */
				if (lu2_g0) {
					/*
					 * 		a <= 0, b <= 0, x >  0, y >  0 => [a / x, b / y]
					 */
					resultLower = l1.div(l2).floor();
					resultUpper = u1.div(u2).floor();
				} else {
					/*
					 * 		a <= 0, b <= 0, x <  0, y <  0 => [b / x, a / y]
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

		return m_factory.makeValue(new Interval(resultLower, resultUpper));
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#modulo(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IntervalValue modulo(IAbstractValue<?> value) {
		/*
		 * [a, b] % [x, y] = [0, min(max(|a|, |b|), max(|x|, |y|)-1)]
		 */
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null) return m_factory.makeBottomValue();
		Interval interval = intVal.getValue();
		
		if (m_value.isEmpty() || interval.isEmpty())
			return m_factory.makeBottomValue();

		// [a, a] % [x, x]
		if (m_value.isSingleValueInterval() && interval.isSingleValueInterval()) {
			Rational a = m_value.getLowerBound();
			Rational x = interval.getLowerBound();
			
			BigInteger aInt = a.numerator().divide(a.denominator());
			
			BigInteger xInt = x.numerator().divide(x.denominator());
			
			BigInteger[] dr = aInt.divideAndRemainder(xInt);
			BigInteger r = dr[1].compareTo(BigInteger.ZERO) >= 0 ? dr[1] : xInt.abs().add(dr[1]);

			return m_factory.makeIntegerValue(r.toString());
		}

		// rationals for calculations
		Rational l1 = m_value.getLowerBound();
		Rational u1 = m_value.getUpperBound();
		Rational l2 = interval.getLowerBound();
		Rational u2 = interval.getUpperBound();
		
		// check for division by zero
		if ((l2.signum() <= 0) && (u2.signum() >= 0)) {
			m_logger.warn(String.format("Potential modulo division by zero: %s %% %s", m_value.toString(), interval.toString()));
			return m_factory.makeBottomValue();
		}

		Rational max1 = l1.compareTo(u1) > 0 ? l1 : u1;
		
		Rational max2 = l2.compareTo(u2) > 0 ? l2 : u2;
		max2 = max2.sub(Rational.ONE);
		
		if (max1.compareTo(max2) < 0)
			return m_factory.makeValue(new Interval(Rational.ZERO, max1));

		return m_factory.makeValue(new Interval(Rational.ZERO, max2));
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#negative()
	 */
	@Override
	public IntervalValue negative() {
		return m_factory.makeValue(new Interval(m_value.getUpperBound().negate(), m_value.getLowerBound().negate()));
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IntervalValue compareIsEqual(IAbstractValue<?> value) {
		/*
			[a, b] == [x, y] => [max(a, x), min(b, y)]
		*/
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null) return m_factory.makeBottomValue();
		Interval interval = intVal.getValue();
		
		if (m_value.isEmpty() || interval.isEmpty())
			return m_factory.makeBottomValue();

		// rationals for calculations
		Rational l1 = m_value.getLowerBound();
		Rational u1 = m_value.getUpperBound();
		Rational l2 = interval.getLowerBound();
		Rational u2 = interval.getUpperBound();

		Rational resultLower = l1.compareTo(l2) > 0 ? l1 : l2;

		Rational resultUpper = u1.compareTo(u2) < 0 ? u1 : u2;
		
		return m_factory.makeValue(new Interval(resultLower, resultUpper));
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsNotEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IntervalValue compareIsNotEqual(IAbstractValue<?> value) {
		/*
			[a, b] != [x, y] => [min(a, x), max(b, y)]
			[a, a] != [a, a] => empty
		*/
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null) return m_factory.makeBottomValue();
		Interval interval = intVal.getValue();
		
		if (m_value.isEmpty() || interval.isEmpty())
			return m_factory.makeBottomValue();

		// rationals for calculations
		Rational l1 = m_value.getLowerBound();
		Rational u1 = m_value.getUpperBound();
		Rational l2 = interval.getLowerBound();
		Rational u2 = interval.getUpperBound();
		
		// [a, a] != [a, a] => empty
		if (m_value.isSingleValueInterval()
				&& interval.isSingleValueInterval()
				&& (l1.compareTo(l2) == 0))
			return m_factory.makeBottomValue();

		Rational resultLower = l1.compareTo(l2) < 0 ? l1 : l2;

		Rational resultUpper = u1.compareTo(u2) > 0 ? u1 : u2;
		
		return m_factory.makeValue(new Interval(resultLower, resultUpper));
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsLess(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IntervalValue compareIsLess(IAbstractValue<?> value) {
		/*
			[a, b] <  [x, y] => [a, min(b, y - 1)]
		*/
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null) return m_factory.makeBottomValue();
		Interval interval = intVal.getValue();
		
		if (m_value.isEmpty() || interval.isEmpty())
			return m_factory.makeBottomValue();

		// rationals for calculations
		Rational u1 = m_value.getUpperBound();
		Rational u2m1 = interval.getUpperBound().sub(Rational.ONE);
		
		Rational resultUpper = u1.compareTo(u2m1) < 0 ? u1 : u2m1;

		return m_factory.makeValue(new Interval(m_value.getLowerBound(), resultUpper));
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsGreater(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IntervalValue compareIsGreater(IAbstractValue<?> value) {
		/*
			[a, b] >  [x, y] => [max(a, x + 1), b]
		*/
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null) return m_factory.makeBottomValue();
		Interval interval = intVal.getValue();
		
		if (m_value.isEmpty() || interval.isEmpty())
			return m_factory.makeBottomValue();

		// rationals for calculations
		Rational l1 = m_value.getLowerBound();
		Rational l2p1 = interval.getLowerBound().add(Rational.ONE);
		
		Rational resultLower = l1.compareTo(l2p1) > 0 ? l1 : l2p1;
	
		return m_factory.makeValue(new Interval(resultLower, m_value.getUpperBound()));
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsLessEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IntervalValue compareIsLessEqual(IAbstractValue<?> value) {
		/*
			[a, b] <= [x, y] => [a, min(b, y)]
		*/
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null) return m_factory.makeBottomValue();
		Interval interval = intVal.getValue();
		
		if (m_value.isEmpty() || interval.isEmpty())
			return m_factory.makeBottomValue();

		// rationals for calculations
		Rational u1 = m_value.getUpperBound();
		Rational u2 = interval.getUpperBound();
		
		Rational resultUpper = u1.compareTo(u2) < 0 ? u1 : u2;
	
		return m_factory.makeValue(new Interval(m_value.getLowerBound(), resultUpper));
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsGreaterEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IntervalValue compareIsGreaterEqual(IAbstractValue<?> value) {
		/*
			[a, b] >= [x, y] => [max(a, x), b]
		*/
		IntervalValue intVal = (IntervalValue) value;
		if (intVal == null) return m_factory.makeBottomValue();
		Interval interval = intVal.getValue();
		
		if (m_value.isEmpty() || interval.isEmpty())
			return m_factory.makeBottomValue();

		// rationals for calculations
		Rational l1 = m_value.getLowerBound();
		Rational l2 = interval.getLowerBound();
		
		Rational resultLower = l1.compareTo(l2) > 0 ? l1 : l2;
	
		return m_factory.makeValue(new Interval(resultLower, m_value.getUpperBound()));
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#logicIff(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IntervalValue logicIff(IAbstractValue<?> value) {
		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#logicImplies(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IntervalValue logicImplies(IAbstractValue<?> value) {
		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#logicAnd(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IntervalValue logicAnd(IAbstractValue<?> value) {
		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#logicOr(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IntervalValue logicOr(IAbstractValue<?> value) {
		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#logicNot()
	 */
	@Override
	public IntervalValue logicNot() {
		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#bitVectorConcat(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IntervalValue bitVectorConcat(IAbstractValue<?> value) {
		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#bitVectorAccess(int, int)
	 */
	@Override
	public IntervalValue bitVectorAccess(int start, int end) {
		return m_factory.makeBottomValue();
	}

	public String toString() {
		return "Interval: " + m_value.toString();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#setIdentifier(java.lang.String, boolean)
	 */
	@Override
	public void setIdentifier(String identifier, boolean isGlobal) {
		// TODO Auto-generated method stub
		
	}
}
