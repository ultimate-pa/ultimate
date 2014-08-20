/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;

/**
 * @author Christopher Dillo
 *
 */
public class SignValue implements IAbstractValue<SignValue.Sign> {
	
	/**
	 * Possible values for the sign domain.
	 * EMPTY < ZERO, PLUS, MINUS < PLUSMINUS
	 * ZERO, PLUS, MINUS : no relation
	 * ZERO : 0
	 * PLUS : > 0
	 * MINUS : < 0
	 */
	public enum Sign {
		EMPTY, ZERO, PLUS, MINUS, PLUSMINUS
	}
	
	private Sign m_value;
	
	private SignDomainFactory m_factory;
	
	private Logger m_logger;
	
	/**
	 * Generate a new SignValue with the given value
	 * @param value ZERO? PLUSMINUS?
	 */
	protected SignValue(Sign value, SignDomainFactory factory, Logger logger) {
		m_value = value;
		m_factory = factory;
		m_logger = logger;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#getValue()
	 */
	@Override
	public Sign getValue() {
		return m_value;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#isTop()
	 */
	@Override
	public boolean isTop() {
		return (m_value == Sign.PLUSMINUS);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#isBottom()
	 */
	@Override
	public boolean isBottom() {
		return (m_value == Sign.EMPTY);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#representsSingleConcreteValue()
	 */
	@Override
	public boolean representsSingleConcreteValue() {
		return (m_value == Sign.PLUS) || (m_value == Sign.MINUS) || (m_value == Sign.ZERO);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#isEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean isEqual(IAbstractValue<?> value) {
		if (value == null)
			return false;
		
		return (m_value == value.getValue());
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#isGreater(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean isSuper(IAbstractValue<?> value) {
		if (value == null)
			return false;
		
		if (m_value == Sign.PLUSMINUS)
			return true;
		
		if (m_value == value.getValue())
			return true;
		
		if (value.getValue() == Sign.EMPTY)
			return true;
		
		return false;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#isLesser(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean isSub(IAbstractValue<?> value) {
		if (value == null)
			return false;
		
		if (m_value == Sign.EMPTY)
			return true;
		
		if (m_value == value.getValue())
			return true;
		
		if (value.getValue() == Sign.PLUSMINUS)
			return true;
		
		return false;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#copy()
	 */
	@Override
	public SignValue copy() {
		return m_factory.makeValue(m_value);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#add(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue add(IAbstractValue<?> value) {
		Sign otherSign = (Sign) value.getValue();
		if (otherSign == null) return m_factory.makeValue(Sign.EMPTY);
		
		switch (m_value) {
		case ZERO :
			return m_factory.makeValue(otherSign);
		case PLUS :
			switch (otherSign) {
			case ZERO :
			case PLUS :
				return m_factory.makeValue(Sign.PLUS);
			case MINUS :
			case PLUSMINUS :
				return m_factory.makeValue(Sign.PLUSMINUS);
			default :
				return m_factory.makeValue(Sign.EMPTY);
			}
		case MINUS :
			switch (otherSign) {
			case ZERO :
			case MINUS :
				return m_factory.makeValue(Sign.MINUS);
			case PLUS :
			case PLUSMINUS :
				return m_factory.makeValue(Sign.PLUSMINUS);
			default :
				return m_factory.makeValue(Sign.EMPTY);
			}
		case PLUSMINUS :
			return m_factory.makeValue(Sign.PLUSMINUS);
		default :
			return m_factory.makeValue(Sign.EMPTY);
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#subtract(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue subtract(IAbstractValue<?> value) {
		Sign otherSign = (Sign) value.getValue();
		if (otherSign == null) return m_factory.makeValue(Sign.EMPTY);
		
		switch (m_value) {
		case ZERO :
			switch (otherSign) {
			case ZERO :
			case PLUSMINUS :
				return m_factory.makeValue(otherSign);
			case PLUS :
				return m_factory.makeValue(Sign.MINUS);
			case MINUS :
				return m_factory.makeValue(Sign.PLUS);
			default :
				return m_factory.makeValue(Sign.EMPTY);
			}
		case PLUS :
			switch (otherSign) {
			case ZERO :
			case MINUS :
				return m_factory.makeValue(Sign.PLUS);
			case PLUS :
			case PLUSMINUS :
				return m_factory.makeValue(Sign.PLUSMINUS);
			default :
				return m_factory.makeValue(Sign.EMPTY);
			}
		case MINUS :
			switch (otherSign) {
			case ZERO :
			case PLUS :
				return m_factory.makeValue(Sign.MINUS);
			case MINUS :
			case PLUSMINUS :
				return m_factory.makeValue(Sign.PLUSMINUS);
			default :
				return m_factory.makeValue(Sign.EMPTY);
			}
		case PLUSMINUS :
			return m_factory.makeValue(Sign.PLUSMINUS);
		default :
			return m_factory.makeValue(Sign.EMPTY);
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#multiply(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue multiply(IAbstractValue<?> value) {
		Sign otherSign = (Sign) value.getValue();
		if (otherSign == null) return m_factory.makeValue(Sign.EMPTY);
		
		switch (m_value) {
		case ZERO :
			return m_factory.makeValue(Sign.ZERO);
		case PLUS :
			switch (otherSign) {
			case ZERO :
				return m_factory.makeValue(Sign.ZERO);
			case PLUS :
				return m_factory.makeValue(Sign.PLUS);
			case MINUS :
				return m_factory.makeValue(Sign.MINUS);
			case PLUSMINUS :
				return m_factory.makeValue(Sign.PLUSMINUS);
			default :
				return m_factory.makeValue(Sign.EMPTY);
			}
		case MINUS :
			switch (otherSign) {
			case ZERO :
				return m_factory.makeValue(Sign.ZERO);
			case PLUS :
				return m_factory.makeValue(Sign.MINUS);
			case MINUS :
				return m_factory.makeValue(Sign.PLUS);
			case PLUSMINUS :
				return m_factory.makeValue(Sign.PLUSMINUS);
			default :
				return m_factory.makeValue(Sign.EMPTY);
			}
		case PLUSMINUS :
			return m_factory.makeValue(Sign.PLUSMINUS);
		default :
			return m_factory.makeValue(Sign.EMPTY);
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#divide(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue divide(IAbstractValue<?> value) {
		if (value == null) return m_factory.makeValue(Sign.EMPTY);
		
		if ((value.getValue() == Sign.ZERO) || (value.getValue() == Sign.PLUSMINUS)) {
			m_logger.warn(String.format("Potential division by zero: %s / %s", this, value));
			return m_factory.makeValue(Sign.EMPTY);
		}
		
		return this.multiply(value);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#modulo(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue modulo(IAbstractValue<?> value) {
		if (value == null) return m_factory.makeValue(Sign.EMPTY);

		if ((value.getValue() == Sign.ZERO) || (value.getValue() == Sign.PLUSMINUS)) {
			m_logger.warn(String.format("Potential modulo division by zero: %s %% %s", this, value));
			return m_factory.makeValue(Sign.EMPTY);
		}
		
		return m_factory.makeValue(Sign.PLUSMINUS); // remainder is always >= 0, which is only covered by PLUSMINUS
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#negation()
	 */
	@Override
	public SignValue negative() {
		switch (m_value) {
		case PLUS :
			return m_factory.makeValue(Sign.MINUS);
		case MINUS :
			return m_factory.makeValue(Sign.PLUS);
		default :
			return m_factory.makeValue(m_value);
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue compareIsEqual(IAbstractValue<?> value) {
		Sign otherSign = (Sign) value.getValue();
		if (otherSign == null) return m_factory.makeValue(Sign.EMPTY);
		
		if (m_value == otherSign)
			return m_factory.makeValue(m_value);
		
		switch (m_value) {
		case ZERO :
			switch (otherSign) {
			case ZERO :
			case PLUSMINUS :
				return m_factory.makeValue(Sign.ZERO);
			case MINUS :
			case PLUS :
			default :
				return m_factory.makeValue(Sign.EMPTY);
			}
		case PLUS :
			switch (otherSign) {
			case PLUS :
			case PLUSMINUS :
				return m_factory.makeValue(Sign.PLUS);
			case ZERO :
			case MINUS :
			default :
				return m_factory.makeValue(Sign.EMPTY);
			}
		case MINUS :
			switch (otherSign) {
			case MINUS :
			case PLUSMINUS :
				return m_factory.makeValue(Sign.MINUS);
			case ZERO :
			case PLUS :
			default :
				return m_factory.makeValue(Sign.EMPTY);
			}
		case PLUSMINUS :
			return m_factory.makeValue(otherSign);
		default :
			return m_factory.makeValue(Sign.EMPTY);
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsNotEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue compareIsNotEqual(IAbstractValue<?> value) {
		Sign otherSign = (Sign) value.getValue();
		if (otherSign == null) return m_factory.makeValue(Sign.EMPTY);
		
		switch (m_value) {
		case ZERO :
			switch (otherSign) {
			case ZERO :
				return m_factory.makeValue(Sign.EMPTY);
			default :
				return m_factory.makeValue(otherSign);
			}
		case PLUS :
			switch (otherSign) {
			case PLUS :
				return m_factory.makeValue(Sign.PLUS);
			case ZERO :
			case MINUS :
			case PLUSMINUS :
				return m_factory.makeValue(Sign.PLUSMINUS);
			default :
				return m_factory.makeValue(Sign.EMPTY);
			}
		case MINUS :
			switch (otherSign) {
			case MINUS :
				return m_factory.makeValue(Sign.MINUS);
			case PLUS :
			case ZERO :
			case PLUSMINUS :
				return m_factory.makeValue(Sign.PLUSMINUS);
			default :
				return m_factory.makeValue(Sign.EMPTY);
			}
		case PLUSMINUS :
			return m_factory.makeValue(Sign.PLUSMINUS);
		default :
			return m_factory.makeValue(Sign.EMPTY);
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsLess(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue compareIsLess(IAbstractValue<?> value) {
		Sign otherSign = (Sign) value.getValue();
		if (otherSign == null) return m_factory.makeValue(Sign.EMPTY);
		
		switch (m_value) {
		case ZERO :
			switch (otherSign) {
			case PLUS :
			case PLUSMINUS :
				return m_factory.makeValue(Sign.ZERO);
			case ZERO :
			case MINUS :
			default :
				return m_factory.makeValue(Sign.EMPTY);
			}
		case PLUS :
			switch (otherSign) {
			case PLUS :
			case PLUSMINUS :
				return m_factory.makeValue(Sign.PLUS);
			case ZERO :
			case MINUS :
			default :
				return m_factory.makeValue(Sign.EMPTY);
			}
		case MINUS :
			return m_factory.makeValue((otherSign == Sign.EMPTY) ? Sign.EMPTY : Sign.MINUS);
		case PLUSMINUS :
			switch (otherSign) {
			case ZERO :
			case MINUS :
				return m_factory.makeValue(Sign.MINUS);
			case PLUS :
			case PLUSMINUS :
				return m_factory.makeValue(Sign.PLUSMINUS);
			default :
				return m_factory.makeValue(Sign.EMPTY);
			}
		default :
			return m_factory.makeValue(Sign.EMPTY);
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsGreater(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue compareIsGreater(IAbstractValue<?> value) {
		Sign otherSign = (Sign) value.getValue();
		if (otherSign == null) return m_factory.makeValue(Sign.EMPTY);
		
		switch (m_value) {
		case ZERO :
			switch (otherSign) {
			case MINUS :
			case PLUSMINUS :
				return m_factory.makeValue(Sign.ZERO);
			case ZERO :
			case PLUS :
			default :
				return m_factory.makeValue(Sign.EMPTY);
			}
		case PLUS :
			return m_factory.makeValue((otherSign == Sign.EMPTY) ? Sign.EMPTY : Sign.PLUS);
		case MINUS :
			switch (otherSign) {
			case MINUS :
			case PLUSMINUS :
				return m_factory.makeValue(Sign.MINUS);
			case ZERO :
			case PLUS :
			default :
				return m_factory.makeValue(Sign.EMPTY);
			}
		case PLUSMINUS :
			switch (otherSign) {
			case ZERO :
			case PLUS :
				return m_factory.makeValue(Sign.PLUS);
			case MINUS :
			case PLUSMINUS :
				return m_factory.makeValue(Sign.PLUSMINUS);
			default :
				return m_factory.makeValue(Sign.EMPTY);
			}
		default :
			return m_factory.makeValue(Sign.EMPTY);
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsLessEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue compareIsLessEqual(IAbstractValue<?> value) {
		Sign otherSign = (Sign) value.getValue();
		if (otherSign == null) return m_factory.makeValue(Sign.EMPTY);
		
		switch (m_value) {
		case ZERO :
			switch (otherSign) {
			case ZERO :
			case PLUS :
			case PLUSMINUS :
				return m_factory.makeValue(Sign.ZERO);
			case MINUS :
			default :
				return m_factory.makeValue(Sign.EMPTY);
			}
		case PLUS :
			switch (otherSign) {
			case PLUS :
			case PLUSMINUS :
				return m_factory.makeValue(Sign.PLUS);
			case ZERO :
			case MINUS :
			default :
				return m_factory.makeValue(Sign.EMPTY);
			}
		case MINUS :
			return m_factory.makeValue((otherSign == Sign.EMPTY) ? Sign.EMPTY : Sign.MINUS);
		case PLUSMINUS :
			switch (otherSign) {
			case ZERO :
			case MINUS :
				return m_factory.makeValue(Sign.MINUS);
			case PLUS :
			case PLUSMINUS :
				return m_factory.makeValue(Sign.PLUSMINUS);
			default :
				return m_factory.makeValue(Sign.EMPTY);
			}
		default :
			return m_factory.makeValue(Sign.EMPTY);
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsGreaterEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue compareIsGreaterEqual(IAbstractValue<?> value) {
		Sign otherSign = (Sign) value.getValue();
		if (otherSign == null) return m_factory.makeValue(Sign.EMPTY);
		
		switch (m_value) {
		case ZERO :
			switch (otherSign) {
			case ZERO :
			case MINUS :
			case PLUSMINUS :
				return m_factory.makeValue(Sign.ZERO);
			case PLUS :
			default :
				return m_factory.makeValue(Sign.EMPTY);
			}
		case PLUS :
			return m_factory.makeValue((otherSign == Sign.EMPTY) ? Sign.EMPTY : Sign.PLUS);
		case MINUS :
			switch (otherSign) {
			case MINUS :
			case PLUSMINUS :
				return m_factory.makeValue(Sign.MINUS);
			case ZERO :
			case PLUS :
			default :
				return m_factory.makeValue(Sign.EMPTY);
			}
		case PLUSMINUS :
			switch (otherSign) {
			case ZERO :
			case PLUS :
				return m_factory.makeValue(Sign.PLUS);
			case MINUS :
			case PLUSMINUS :
				return m_factory.makeValue(Sign.PLUSMINUS);
			default :
				return m_factory.makeValue(Sign.EMPTY);
			}
		default :
			return m_factory.makeValue(Sign.EMPTY);
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#logicIff(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue logicIff(IAbstractValue<?> value) {
		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#logicImplies(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue logicImplies(IAbstractValue<?> value) {
		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#logicAnd(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue logicAnd(IAbstractValue<?> value) {
		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#logicOr(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue logicOr(IAbstractValue<?> value) {
		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#logicNot()
	 */
	@Override
	public SignValue logicNot() {
		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#bitVectorConcat(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue bitVectorConcat(IAbstractValue<?> value) {
		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#bitVectorAccess(int, int)
	 */
	@Override
	public SignValue bitVectorAccess(int start, int end) {
		return m_factory.makeBottomValue();
	}

	@Override
	public String toString() {
		switch (m_value) {
		case ZERO :
			return "Sign: 0";
		case PLUS :
			return "Sign: +";
		case MINUS :
			return "Sign: -";
		case PLUSMINUS :
			return "Sign: +-";
		default :
			return "Sign: empty";
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#setIdentifier(java.lang.String, boolean)
	 */
	@Override
	public void setIdentifier(String identifier, boolean isGlobal) {
		// TODO Auto-generated method stub
		
	}
}
