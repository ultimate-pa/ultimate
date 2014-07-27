/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.intervaldomain;

import java.math.BigInteger;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;

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
		return m_value.lowerBoundIsNegInfty() && m_value.upperBoundIsPosInfty();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#isBottom()
	 */
	@Override
	public boolean isBottom() {
		return m_value.isEmpty();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#isEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean isEqual(IAbstractValue<?> value) {
		Interval interval = (Interval) value.getValue();
		if (interval == null) return false;

		return m_value.equals(interval);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#isSuper(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean isSuper(IAbstractValue<?> value) {
		Interval interval = (Interval) value.getValue();
		if (interval == null) return false;
		
		boolean lowerIsLessEq, upperIsGreaterEq;
		
		if (interval.lowerBoundIsNegInfty()) {
			if (!m_value.lowerBoundIsNegInfty())
				return false;
			lowerIsLessEq = true;
		} else {
			if (m_value.lowerBoundIsNegInfty()) {
				lowerIsLessEq = true;
			} else {
				BigInteger l1 = new BigInteger(m_value.getLowerBound());
				BigInteger l2 = new BigInteger(interval.getLowerBound());
				lowerIsLessEq = l1.compareTo(l2) <= 0;
			}
		}

		if (interval.upperBoundIsPosInfty()) {
			if (!m_value.upperBoundIsPosInfty())
				return false;
			upperIsGreaterEq = true;
		} else {
			if (m_value.upperBoundIsPosInfty()) {
				upperIsGreaterEq = true;
			} else {
				BigInteger u1 = new BigInteger(m_value.getUpperBound());
				BigInteger u2 = new BigInteger(interval.getUpperBound());
				upperIsGreaterEq = u1.compareTo(u2) >= 0;
			}
		}
		
		return lowerIsLessEq && upperIsGreaterEq;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#isSub(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean isSub(IAbstractValue<?> value) {
		Interval interval = (Interval) value.getValue();
		if (interval == null) return false;
		
		boolean lowerIsGreaterEq, upperIsLessEq;
		
		if (interval.lowerBoundIsNegInfty()) {
			if (!m_value.lowerBoundIsNegInfty())
				return false;
			lowerIsGreaterEq = true;
		} else {
			if (m_value.lowerBoundIsNegInfty()) {
				lowerIsGreaterEq = true;
			} else {
				BigInteger l1 = new BigInteger(m_value.getLowerBound());
				BigInteger l2 = new BigInteger(interval.getLowerBound());
				lowerIsGreaterEq = l1.compareTo(l2) >= 0;
			}
		}
		
		if (interval.upperBoundIsPosInfty()) {
			if (!m_value.upperBoundIsPosInfty())
				return false;
			upperIsLessEq = true;
		} else {
			if (m_value.upperBoundIsPosInfty()) {
				upperIsLessEq = true;
			} else {
				BigInteger u1 = new BigInteger(m_value.getUpperBound());
				BigInteger u2 = new BigInteger(interval.getUpperBound());
				upperIsLessEq = u1.compareTo(u2) <= 0;
			}
		}
		
		return lowerIsGreaterEq && upperIsLessEq;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#copy()
	 */
	@Override
	public IAbstractValue<Interval> copy() {
		return m_factory.makeValue(m_value.copy());
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#add(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IAbstractValue<Interval> add(IAbstractValue<?> value) {
		/*
		 * [a, b] + [x, y] = [a + x, b + y]
		 */
		
		Interval interval = (Interval) value.getValue();
		if (interval == null) return m_factory.makeBottomValue();
		
		String resultLower, resultUpper;
		
		if (m_value.lowerBoundIsNegInfty() || interval.lowerBoundIsNegInfty()) {
			resultLower = null; // -> -infty
		} else {
			BigInteger l1 = new BigInteger(m_value.getLowerBound());
			BigInteger l2 = new BigInteger(interval.getLowerBound());
			
			resultLower = l1.add(l2).toString();
		}

		if (m_value.upperBoundIsPosInfty() || interval.upperBoundIsPosInfty()) {
			resultUpper = null; // -> +infty
		} else {
			BigInteger u1 = new BigInteger(m_value.getUpperBound());
			BigInteger u2 = new BigInteger(interval.getUpperBound());
			
			resultUpper = u1.add(u2).toString();
		}
		
		return m_factory.makeValue(new Interval(resultLower, resultUpper));
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#subtract(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IAbstractValue<Interval> subtract(IAbstractValue<?> value) {
		/*
		 * [a, b] - [x, y] = [a - y, b - x]
		 */
		
		Interval interval = (Interval) value.getValue();
		if (interval == null) return m_factory.makeBottomValue();
		
		String resultLower, resultUpper;
		
		if (m_value.lowerBoundIsNegInfty() || interval.upperBoundIsPosInfty()) {
			resultLower = null; // -> -infty
		} else {
			BigInteger l1 = new BigInteger(m_value.getLowerBound());
			BigInteger u2 = new BigInteger(interval.getUpperBound());
			
			resultLower = l1.subtract(u2).toString();
		}
	
		if (m_value.upperBoundIsPosInfty() || interval.lowerBoundIsNegInfty()) {
			resultUpper = null; // -> +infty
		} else {
			BigInteger u1 = new BigInteger(m_value.getUpperBound());
			BigInteger l2 = new BigInteger(interval.getLowerBound());
			
			resultUpper = u1.subtract(l2).toString();
		}
		
		return m_factory.makeValue(new Interval(resultLower, resultUpper));
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#multiply(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IAbstractValue<Interval> multiply(IAbstractValue<?> value) {
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
		
		Interval interval = (Interval) value.getValue();
		if (interval == null) return m_factory.makeBottomValue();

		String resultLower, resultUpper;

		// big integers for calculations
		BigInteger l1 = m_value.lowerBoundIsNegInfty() ? null : new BigInteger(m_value.getLowerBound());
		BigInteger u1 = m_value.upperBoundIsPosInfty() ? null : new BigInteger(m_value.getUpperBound());
		BigInteger l2 = interval.lowerBoundIsNegInfty() ? null : new BigInteger(interval.getLowerBound());
		BigInteger u2 = interval.upperBoundIsPosInfty() ? null : new BigInteger(interval.getUpperBound());

		// flags for sign checks
		boolean l1_geq0 = !m_value.lowerBoundIsNegInfty() && (l1.compareTo(BigInteger.ZERO) >= 0);
		boolean u1_geq0 = m_value.upperBoundIsPosInfty() || (u1.compareTo(BigInteger.ZERO) >= 0);
		boolean l2_geq0 = !interval.lowerBoundIsNegInfty() && (l2.compareTo(BigInteger.ZERO) >= 0);
		boolean u2_geq0 = interval.upperBoundIsPosInfty() || (u2.compareTo(BigInteger.ZERO) >= 0);
		
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
				resultLower = l1.multiply(l2).toString();
				if (m_value.upperBoundIsPosInfty() || interval.upperBoundIsPosInfty()) {
					resultUpper = null; // -> +infty
				} else {
					resultUpper = u1.multiply(u2).toString();
				}
			} else {
				/*
				 * 	a >= 0, b >= 0, x <= 0, y >= 0 => [b * x, b * y]
				 * 	a >= 0, b >= 0, x <= 0, y <= 0 => [b * x, a * y]
				 */
				if (m_value.upperBoundIsPosInfty()) {
					resultLower = null; // -> -infty
				} else {
					resultLower = u1.multiply(l2).toString();
				}
				if (u2_geq0) {
					/*
					 * 	a >= 0, b >= 0, x <= 0, y >= 0 => [b * x, b * y]
					 */
					if (m_value.upperBoundIsPosInfty() || interval.upperBoundIsPosInfty()) {
						resultUpper = null; // -> +infty
					} else {
						resultUpper = u1.multiply(u2).toString();
					}
				} else {
					/*
					 * 	a >= 0, b >= 0, x <= 0, y <= 0 => [b * x, a * y]
					 */
					resultUpper = l1.multiply(u2).toString();
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
					if (m_value.lowerBoundIsNegInfty() || interval.upperBoundIsPosInfty()) {
						resultLower = null; // -> -infty
					} else {
						resultLower = l1.multiply(u2).toString();
					}
					if (m_value.upperBoundIsPosInfty() || interval.upperBoundIsPosInfty()) {
						resultUpper = null; // -> +infty
					} else {
						resultUpper = u1.multiply(u2).toString();
					}
				} else {
					/*
					 * 	a <= 0, b >= 0, x <= 0, y >= 0 => [min(a * y, b * x), max(a * x, b * y)]
					 * 	a <= 0, b >= 0, x <= 0, y <= 0 => [b * x, a * x]
					 */
					if (u2_geq0) {
						/*
						 * 	a <= 0, b >= 0, x <= 0, y >= 0 => [min(a * y, b * x), max(a * x, b * y)]
						 */
						if (m_value.lowerBoundIsNegInfty() || interval.upperBoundIsPosInfty()
								|| m_value.upperBoundIsPosInfty() || interval.lowerBoundIsNegInfty()) {
							resultLower = null; // -> -infty
							resultUpper = null; // -> +infty
						} else {
							BigInteger l1u2 = l1.multiply(u2);
							BigInteger u1l2 = u1.multiply(l2);
							resultLower = ((l1u2.compareTo(u1l2) < 0) ? l1u2 : u1l2).toString();
							BigInteger l1l2 = l1.multiply(l2);
							BigInteger u1u2 = u1.multiply(u2);
							resultUpper = ((l1l2.compareTo(u1u2) > 0) ? l1l2 : u1u2).toString();
						}
					} else {
						/*
						 * 	a <= 0, b >= 0, x <= 0, y <= 0 => [b * x, a * x]
						 */
						if (m_value.upperBoundIsPosInfty() || interval.lowerBoundIsNegInfty()) {
							resultLower = null; // -> -infty
						} else {
							resultLower = u1.multiply(l2).toString();
						}
						if (m_value.lowerBoundIsNegInfty() || interval.lowerBoundIsNegInfty()) {
							resultUpper = null; // -> +infty
						} else {
							resultUpper = l1.multiply(l2).toString();
						}
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
					if (m_value.lowerBoundIsNegInfty() || interval.upperBoundIsPosInfty()) {
						resultLower = null; // -> -infty
					} else {
						resultLower = l1.multiply(u2).toString();
					}
					resultUpper = u1.multiply(l2).toString();
				} else {
					/*
					 * 	a <= 0, b <= 0, x <= 0, y >= 0 => [a * y, max(a * x, b * y)]
					 * 	a <= 0, b <= 0, x <= 0, y <= 0 => [b * y, a * x]
					 */
					if (u2_geq0) {
						/*
						 * 	a <= 0, b <= 0, x <= 0, y >= 0 => [a * y, max(a * x, b * y)]
						 */
						if (m_value.lowerBoundIsNegInfty() || interval.upperBoundIsPosInfty()) {
							resultLower = null; // -> -infty
						} else {
							resultLower = l1.multiply(u2).toString();
						}
						if (m_value.lowerBoundIsNegInfty() || interval.lowerBoundIsNegInfty()
								|| m_value.upperBoundIsPosInfty() || interval.upperBoundIsPosInfty()) {
							resultUpper = null; // -> +infty
						} else {
							BigInteger l1l2 = l1.multiply(l2);
							BigInteger u1u2 = u1.multiply(u2);
							resultUpper = ((l1l2.compareTo(u1u2) > 0) ? l1l2 : u1u2).toString();
						}
					} else {
						/*
						 * 	a <= 0, b <= 0, x <= 0, y <= 0 => [b * y, a * x]
						 */
						resultLower = u1.multiply(u2).toString();
						if (m_value.lowerBoundIsNegInfty() || interval.lowerBoundIsNegInfty()) {
							resultUpper = null; // -> +infty
						} else {
							resultUpper = l1.multiply(l2).toString();
						}
					}
				}
			}
		}

		return m_factory.makeValue(new Interval(resultLower, resultUpper));
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#divide(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IAbstractValue<Interval> divide(IAbstractValue<?> value) {
		/*
		 * [a, b] / [x, y] = [floor(min(a / x, a / y, b / x, b / y)),
		 * 					ceil(max(a / x, a / y, b / x, b / y))]
		 * Potential division by zero -> Warning/Error, value to (-infty, infty) ///// BOTTOM!!
		 * Optimisations by taking signs into account:
		 * 		a >= 0, b >= 0, x >  0, y >  0 => [floor(a / y), ceil(b / x)]
		 * 		a >= 0, b >= 0, x <  0, y <  0 => [floor(b / y), ceil(a / x)]
		 * 		a <= 0, b >= 0, x >  0, y >  0 => [floor(a / x), ceil(b / x)]
		 * 		a <= 0, b >= 0, x <  0, y <  0 => [floor(b / y), ceil(a / y)]
		 * 		a <= 0, b <= 0, x >  0, y >  0 => [floor(a / x), ceil(b / y)]
		 * 		a <= 0, b <= 0, x <  0, y <  0 => [floor(b / x), ceil(a / y)]
				                x <= 0, y >= 0 => (-infty, infty), Warning/Error
		 */
		
		Interval interval = (Interval) value.getValue();
		if (interval == null) return m_factory.makeBottomValue();

		String resultLower, resultUpper;

		// big integers for calculations
		BigInteger l1 = m_value.lowerBoundIsNegInfty() ? null : new BigInteger(m_value.getLowerBound());
		BigInteger u1 = m_value.upperBoundIsPosInfty() ? null : new BigInteger(m_value.getUpperBound());
		BigInteger l2 = interval.lowerBoundIsNegInfty() ? null : new BigInteger(interval.getLowerBound());
		BigInteger u2 = interval.upperBoundIsPosInfty() ? null : new BigInteger(interval.getUpperBound());
		
		// check for division by zero
		if ((interval.lowerBoundIsNegInfty() || (l2.compareTo(BigInteger.ZERO) <= 0))
				&& (interval.upperBoundIsPosInfty() || (u2.compareTo(BigInteger.ZERO) >= 0))) {
			m_logger.warn(String.format("Potential division by zero: %s / %s", m_value.toString(), interval.toString()));
			return m_factory.makeBottomValue();
		}

		// flags for sign checks
		boolean l1_geq0 = !m_value.lowerBoundIsNegInfty() && (l1.compareTo(BigInteger.ZERO) >= 0);
		boolean u1_geq0 = m_value.upperBoundIsPosInfty() || (u1.compareTo(BigInteger.ZERO) >= 0);
		boolean lu2_g0 = !interval.lowerBoundIsNegInfty() && (l2.compareTo(BigInteger.ZERO) > 0);
		
		if (l1_geq0) {
			/*
			 * 		a >= 0, b >= 0, x >  0, y >  0 => [floor(a / y), ceil(b / x)]
			 * 		a >= 0, b >= 0, x <  0, y <  0 => [floor(b / y), ceil(a / x)]
			 */
			if (lu2_g0) {
				/*
				 * 		a >= 0, b >= 0, x >  0, y >  0 => [floor(a / y), ceil(b / x)]
				 */
				if (interval.upperBoundIsPosInfty()) {
					resultLower = BigInteger.ZERO.toString();
				} else {
					resultLower = l1.divide(u2).toString();
				}
				if (m_value.upperBoundIsPosInfty()) {
					resultUpper = null;
				} else {
					BigInteger[] upper = u1.divideAndRemainder(l2);
					if (upper[1].equals(BigInteger.ZERO)) {
						resultUpper = upper[0].toString();
					} else {
						resultUpper = upper[0].add(BigInteger.ONE).toString(); // round up!
					}
				}
			} else {
				/*
				 * 		a >= 0, b >= 0, x <  0, y <  0 => [floor(b / y), ceil(a / x)]
				 */
				if (m_value.upperBoundIsPosInfty()) {
					resultLower = null;
				} else {
					BigInteger[] lower = u1.divideAndRemainder(u2);
					if (lower[1].equals(BigInteger.ZERO)) {
						resultLower = lower[0].toString();
					} else {
						resultLower = lower[0].subtract(BigInteger.ONE).toString(); // round down!
					}
				}
				if (interval.lowerBoundIsNegInfty()) {
					resultUpper = BigInteger.ZERO.toString();
				} else {
					resultUpper = l1.divide(l2).toString();
				}
			}
		} else {
			/*
			 * 		a <= 0, b >= 0, x >  0, y >  0 => [floor(a / x), ceil(b / x)]
			 * 		a <= 0, b >= 0, x <  0, y <  0 => [floor(b / y), ceil(a / y)]
			 * 		a <= 0, b <= 0, x >  0, y >  0 => [floor(a / x), ceil(b / y)]
			 * 		a <= 0, b <= 0, x <  0, y <  0 => [floor(b / x), ceil(a / y)]
			 */
			if (u1_geq0) {
				/*
				 * 		a <= 0, b >= 0, x >  0, y >  0 => [floor(a / x), ceil(b / x)]
				 * 		a <= 0, b >= 0, x <  0, y <  0 => [floor(b / y), ceil(a / y)]
				 */
				if (lu2_g0) {
					/*
					 * 		a <= 0, b >= 0, x >  0, y >  0 => [floor(a / x), ceil(b / x)]
					 */
					if (m_value.lowerBoundIsNegInfty()) {
						resultLower = null;
					} else {
						BigInteger[] lower = l1.divideAndRemainder(l2);
						if (lower[1].equals(BigInteger.ZERO)) {
							resultLower = lower[0].toString();
						} else {
							resultLower = lower[0].subtract(BigInteger.ONE).toString(); // round down!
						}
					}
					if (m_value.upperBoundIsPosInfty()) {
						resultUpper = null;
					} else {
						BigInteger[] upper = u1.divideAndRemainder(l2);
						if (upper[1].equals(BigInteger.ZERO)) {
							resultUpper = upper[0].toString();
						} else {
							resultUpper = upper[0].add(BigInteger.ONE).toString(); // round up!
						}
					}
				} else {
					/*
					 * 		a <= 0, b >= 0, x <  0, y <  0 => [floor(b / y), ceil(a / y)]
					 */
					if (m_value.upperBoundIsPosInfty()) {
						resultLower = null;
					} else {
						BigInteger[] lower = u1.divideAndRemainder(u2);
						if (lower[1].equals(BigInteger.ZERO)) {
							resultLower = lower[0].toString();
						} else {
							resultLower = lower[0].subtract(BigInteger.ONE).toString(); // round down!
						}
					}
					if (m_value.lowerBoundIsNegInfty()) {
						resultUpper = null;
					} else {
						BigInteger[] upper = l1.divideAndRemainder(u2);
						if (upper[1].equals(BigInteger.ZERO)) {
							resultUpper = upper[0].toString();
						} else {
							resultUpper = upper[0].add(BigInteger.ONE).toString(); // round up!
						}
					}
				}
			} else {
				/*
				 * 		a <= 0, b <= 0, x >  0, y >  0 => [floor(a / x), ceil(b / y)]
				 * 		a <= 0, b <= 0, x <  0, y <  0 => [floor(b / x), ceil(a / y)]
				 */
				if (lu2_g0) {
					/*
					 * 		a <= 0, b <= 0, x >  0, y >  0 => [floor(a / x), ceil(b / y)]
					 */
					if (m_value.lowerBoundIsNegInfty()) {
						resultLower = null;
					} else {
						BigInteger[] lower = l1.divideAndRemainder(l2);
						if (lower[1].equals(BigInteger.ZERO)) {
							resultLower = lower[0].toString();
						} else {
							resultLower = lower[0].subtract(BigInteger.ONE).toString(); // round down!
						}
					}
					if (interval.upperBoundIsPosInfty()) {
						resultUpper = BigInteger.ZERO.toString();
					} else {
						resultUpper = u1.divide(u2).toString();
					}
				} else {
					/*
					 * 		a <= 0, b <= 0, x <  0, y <  0 => [floor(b / x), ceil(a / y)]
					 */
					if (interval.lowerBoundIsNegInfty()) {
						resultLower = BigInteger.ZERO.toString();
					} else {
						resultLower = u1.divide(l2).toString();
					}
					if (m_value.lowerBoundIsNegInfty()) {
						resultUpper = null;
					} else {
						BigInteger[] upper = l1.divideAndRemainder(u2);
						if (upper[1].equals(BigInteger.ZERO)) {
							resultUpper = upper[0].toString();
						} else {
							resultUpper = upper[0].add(BigInteger.ONE).toString(); // round up!
						}
					}
				}
			}
		}

		return m_factory.makeValue(new Interval(resultLower, resultUpper));
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#modulo(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IAbstractValue<Interval> modulo(IAbstractValue<?> value) {
		/*
		 * [a, b] % [x, y] = [min(a % x, a % y, b % x, b % y),
		 * 					   max(a % x, a % y, b % x, b % y)]
		 */
		
		Interval interval = (Interval) value.getValue();
		if (interval == null) return m_factory.makeBottomValue();

		// big integers for calculations
		BigInteger l1 = m_value.lowerBoundIsNegInfty() ? null : new BigInteger(m_value.getLowerBound());
		BigInteger u1 = m_value.upperBoundIsPosInfty() ? null : new BigInteger(m_value.getUpperBound());
		BigInteger l2 = interval.lowerBoundIsNegInfty() ? null : new BigInteger(interval.getLowerBound());
		BigInteger u2 = interval.upperBoundIsPosInfty() ? null : new BigInteger(interval.getUpperBound());
		
		// check for division by zero
		if ((interval.lowerBoundIsNegInfty() || (l2.compareTo(BigInteger.ZERO) <= 0))
				&& (interval.upperBoundIsPosInfty() || (u2.compareTo(BigInteger.ZERO) >= 0))) {
			m_logger.warn(String.format("Potential modulo division by zero: %s %% %s", m_value.toString(), interval.toString()));
			return m_factory.makeBottomValue();
		}

		// flags for sign checks
		boolean lu2_g0 = !interval.lowerBoundIsNegInfty() && (l2.compareTo(BigInteger.ZERO) > 0);
		
		// l1 % l2
		BigInteger l1ml2 = null;
		boolean l1ml2_negInf = false;
		boolean l1ml2_posInf = false;
		if (m_value.lowerBoundIsNegInfty()) {
			if (lu2_g0) {
				l1ml2_negInf = true;
			} else {
				l1ml2_posInf = true;
			}
		} if (interval.lowerBoundIsNegInfty()) {
			l1ml2 = l1.negate();
		} else {
			l1ml2 = l1.remainder(l2);
		}
		
		// l1 % u2
		BigInteger l1mu2 = null;
		boolean l1mu2_negInf = false;
		boolean l1mu2_posInf = false;
		if (m_value.lowerBoundIsNegInfty()) {
			if (lu2_g0) {
				l1ml2_negInf = true;
			} else {
				l1ml2_posInf = true;
			}
		} if (interval.upperBoundIsPosInfty()) {
			l1mu2 = l1;
		} else {
			l1mu2 = l1.remainder(u2);
		}
		
		// u1 % l2
		BigInteger u1ml2 = null;
		boolean u1ml2_negInf = false;
		boolean u1ml2_posInf = false;
		if (m_value.upperBoundIsPosInfty()) {
			if (lu2_g0) {
				u1ml2_posInf = true;
			} else {
				u1ml2_negInf = true;
			}
		} if (interval.lowerBoundIsNegInfty()) {
			u1ml2 = u1.negate();
		} else {
			u1ml2 = u1.remainder(l2);
		}
		
		// u1 % u2
		BigInteger u1mu2 = null;
		boolean u1mu2_negInf = false;
		boolean u1mu2_posInf = false;
		if (m_value.upperBoundIsPosInfty()) {
			if (lu2_g0) {
				u1mu2_posInf = true;
			} else {
				u1mu2_negInf = true;
			}
		} if (interval.upperBoundIsPosInfty()) {
			u1mu2 = u1;
		} else {
			u1mu2 = u1.remainder(u2);
		}
		
		// determine minimum for lower bound
		BigInteger resultLower = null;
		boolean resultLower_negInf = false;

		if (l1ml2_negInf || l1mu2_negInf || u1ml2_negInf || u1mu2_negInf) {
			resultLower_negInf = true;
		} else {
			resultLower = l1ml2;
			
			if (!l1mu2_posInf && ((resultLower == null) || (l1mu2.compareTo(resultLower) < 0)))
				resultLower = l1mu2;

			if (!u1ml2_posInf && ((resultLower == null) || (u1ml2.compareTo(resultLower) < 0)))
				resultLower = u1ml2;

			if (!u1mu2_posInf && ((resultLower == null) || (u1mu2.compareTo(resultLower) < 0)))
				resultLower = u1mu2;
		}
		
		// determine maximum for upper bound
		BigInteger resultUpper = null;
		boolean resultUpper_posInf = false;

		if (l1ml2_posInf || l1mu2_posInf || u1ml2_posInf || u1mu2_posInf) {
			resultUpper_posInf = true;
		} else {
			resultLower = l1ml2;
			
			if (!l1mu2_negInf && ((resultUpper == null) || (l1mu2.compareTo(resultUpper) > 0)))
				resultUpper = l1mu2;

			if (!u1ml2_negInf && ((resultUpper == null) || (u1ml2.compareTo(resultUpper) > 0)))
				resultUpper = u1ml2;

			if (!u1mu2_negInf && ((resultUpper == null) || (u1mu2.compareTo(resultUpper) > 0)))
				resultUpper = u1mu2;
		}
		
		return m_factory.makeValue(new Interval((resultLower_negInf || (resultLower == null)) ? null : resultLower.toString(),
				(resultUpper_posInf || (resultUpper == null)) ? null : resultUpper.toString()));
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#negative()
	 */
	@Override
	public IAbstractValue<Interval> negative() {
		return m_factory.makeValue(new Interval(m_value.upperBoundIsPosInfty() ? null : m_value.getUpperBound(),
				m_value.lowerBoundIsNegInfty() ? null : m_value.getUpperBound()));
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IAbstractValue<Interval> compareIsEqual(IAbstractValue<?> value) {
		/*
			[a, b] == [x, y] => [max(a, x), min(b, y)]
		*/
		
		Interval interval = (Interval) value.getValue();
		if (interval == null) return m_factory.makeBottomValue();
		
		String resultLower, resultUpper;
		
		if (m_value.lowerBoundIsNegInfty()) {
			if (interval.lowerBoundIsNegInfty()) {
				resultLower = null;
			} else {
				resultLower = interval.getLowerBound();
			}
		} else if (interval.lowerBoundIsNegInfty()) {
			resultLower = m_value.getLowerBound();
		} else {
			BigInteger l1 = new BigInteger(m_value.getLowerBound());
			BigInteger l2 = new BigInteger(interval.getLowerBound());
			if (l1.compareTo(l2) > 0)
				resultLower = m_value.getLowerBound();
			else
				resultLower = interval.getLowerBound();
		}

		if (m_value.upperBoundIsPosInfty()) {
			if (interval.upperBoundIsPosInfty()) {
				resultUpper = null;
			} else {
				resultUpper = interval.getUpperBound();
			}
		} else if (interval.upperBoundIsPosInfty()) {
			resultUpper = m_value.getUpperBound();
		} else {
			BigInteger u1 = new BigInteger(m_value.getUpperBound());
			BigInteger u2 = new BigInteger(interval.getUpperBound());
			if (u1.compareTo(u2) < 0)
				resultUpper = m_value.getUpperBound();
			else
				resultUpper = interval.getUpperBound();
		}
		
		return m_factory.makeValue(new Interval(resultLower, resultUpper));
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsNotEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IAbstractValue<Interval> compareIsNotEqual(IAbstractValue<?> value) {
		/*
			[a, b] != [x, y] => [min(a, x), max(b, y)]
			[a, a] != [a, a] => empty
		*/
		
		Interval interval = (Interval) value.getValue();
		if (interval == null) return m_factory.makeBottomValue();
		
		// [a, a] != [a, a] => empty
		if (!m_value.lowerBoundIsNegInfty()
				&& m_value.getLowerBound().equals(m_value.getUpperBound())
				&& m_value.getLowerBound().equals(interval.getLowerBound())
				&& m_value.getLowerBound().equals(interval.getUpperBound()))
			return m_factory.makeBottomValue();
		
		String resultLower, resultUpper;
		
		if (m_value.lowerBoundIsNegInfty() || interval.lowerBoundIsNegInfty()) {
			resultLower = null;
		} else {
			BigInteger l1 = new BigInteger(m_value.getLowerBound());
			BigInteger l2 = new BigInteger(interval.getLowerBound());
			if (l1.compareTo(l2) < 0)
				resultLower = m_value.getLowerBound();
			else
				resultLower = interval.getLowerBound();
		}

		if (m_value.upperBoundIsPosInfty() || interval.upperBoundIsPosInfty()) {
			resultUpper = null;
		} else {
			BigInteger u1 = new BigInteger(m_value.getUpperBound());
			BigInteger u2 = new BigInteger(interval.getUpperBound());
			if (u1.compareTo(u2) > 0)
				resultUpper = m_value.getUpperBound();
			else
				resultUpper = interval.getUpperBound();
		}
		
		return m_factory.makeValue(new Interval(resultLower, resultUpper));
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsLess(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IAbstractValue<Interval> compareIsLess(IAbstractValue<?> value) {
		/*
			[a, b] <  [x, y] => [a, min(b, y - 1)]
		*/
		
		Interval interval = (Interval) value.getValue();
		if (interval == null) return m_factory.makeBottomValue();

		String resultUpper;
		
		if (m_value.upperBoundIsPosInfty()) {
			if (interval.upperBoundIsPosInfty()) {
				resultUpper = null;
			} else {
				resultUpper = (new BigInteger(interval.getUpperBound())).subtract(BigInteger.ONE).toString();
			}
		} else {
			if (interval.upperBoundIsPosInfty()) {
				resultUpper = m_value.getUpperBound();
			} else {
				BigInteger u1 = new BigInteger(m_value.getUpperBound());
				BigInteger u2 = (new BigInteger(interval.getUpperBound())).subtract(BigInteger.ONE);
				if (u1.compareTo(u2) <= 0) {
					resultUpper = m_value.getUpperBound();
				} else {
					resultUpper = u2.toString();
				}
			}
		}

		return m_factory.makeValue(new Interval(m_value.getLowerBound(), resultUpper));
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsGreater(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IAbstractValue<Interval> compareIsGreater(IAbstractValue<?> value) {
		/*
			[a, b] >  [x, y] => [max(a, x + 1), b]
		*/
		
		Interval interval = (Interval) value.getValue();
		if (interval == null) return m_factory.makeBottomValue();
	
		String resultLower;
		
		if (m_value.lowerBoundIsNegInfty()) {
			if (interval.lowerBoundIsNegInfty()) {
				resultLower = null;
			} else {
				resultLower = (new BigInteger(interval.getLowerBound())).add(BigInteger.ONE).toString();
			}
		} else {
			if (interval.lowerBoundIsNegInfty()) {
				resultLower = m_value.getLowerBound();
			} else {
				BigInteger l1 = new BigInteger(m_value.getLowerBound());
				BigInteger l2 = (new BigInteger(interval.getLowerBound())).add(BigInteger.ONE);
				if (l1.compareTo(l2) >= 0) {
					resultLower = m_value.getLowerBound();
				} else {
					resultLower = l2.toString();
				}
			}
		}
	
		return m_factory.makeValue(new Interval(resultLower, m_value.getUpperBound()));
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsLessEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IAbstractValue<Interval> compareIsLessEqual(IAbstractValue<?> value) {
		/*
			[a, b] <= [x, y] => [a, min(b, y)]
		*/
		
		Interval interval = (Interval) value.getValue();
		if (interval == null) return m_factory.makeBottomValue();
	
		String resultUpper;
		
		if (m_value.upperBoundIsPosInfty()) {
			if (interval.upperBoundIsPosInfty()) {
				resultUpper = null;
			} else {
				resultUpper = interval.getUpperBound();
			}
		} else {
			if (interval.upperBoundIsPosInfty()) {
				resultUpper = m_value.getUpperBound();
			} else {
				BigInteger u1 = new BigInteger(m_value.getUpperBound());
				BigInteger u2 = new BigInteger(interval.getUpperBound());
				if (u1.compareTo(u2) <= 0) {
					resultUpper = m_value.getUpperBound();
				} else {
					resultUpper = interval.getUpperBound();
				}
			}
		}
	
		return m_factory.makeValue(new Interval(m_value.getLowerBound(), resultUpper));
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsGreaterEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IAbstractValue<Interval> compareIsGreaterEqual(IAbstractValue<?> value) {
		/*
			[a, b] >= [x, y] => [max(a, x), b]
		*/
		
		Interval interval = (Interval) value.getValue();
		if (interval == null) return m_factory.makeBottomValue();
	
		String resultLower;
		
		if (m_value.lowerBoundIsNegInfty()) {
			if (interval.lowerBoundIsNegInfty()) {
				resultLower = null;
			} else {
				resultLower = interval.getLowerBound();
			}
		} else {
			if (interval.lowerBoundIsNegInfty()) {
				resultLower = m_value.getLowerBound();
			} else {
				BigInteger l1 = new BigInteger(m_value.getLowerBound());
				BigInteger l2 = new BigInteger(interval.getLowerBound());
				if (l1.compareTo(l2) >= 0) {
					resultLower = m_value.getLowerBound();
				} else {
					resultLower = interval.getLowerBound();
				}
			}
		}
	
		return m_factory.makeValue(new Interval(resultLower, m_value.getUpperBound()));
	}

	public String toString() {
		return "Interval: " + m_value.toString();
	}
}
