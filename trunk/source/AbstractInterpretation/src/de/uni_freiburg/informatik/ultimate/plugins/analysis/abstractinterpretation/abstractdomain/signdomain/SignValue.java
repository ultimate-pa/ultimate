/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.AbstractInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;

/**
 * @author Christopher Dillo
 *
 */
public class SignValue implements IAbstractValue {
	
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
	
	/**
	 * Generate a new SignValue with the given value
	 * @param value ZERO? PLUSMINUS?
	 */
	public SignValue(Sign value) {
		m_value = value;
	}
	
	public Sign getValue() {
		return m_value;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#getDomainID()
	 */
	@Override
	public String getDomainID() {
		return SignDomainFactory.s_DomainID;
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
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#isEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean isEqual(IAbstractValue value) {
		SignValue sval = (SignValue) value;
		
		// incompatible domain system
		if (sval == null)
			return false;
		
		return (m_value == sval.getValue());
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#isGreater(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean isSuper(IAbstractValue value) {
		SignValue sval = (SignValue) value;
		
		// incompatible domain system
		if (sval == null)
			return false;
		
		if (m_value == Sign.PLUSMINUS)
			return true;
		
		if (m_value == sval.getValue())
			return true;
		
		if (sval.getValue() == Sign.EMPTY)
			return true;
		
		return false;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#isLesser(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean isSub(IAbstractValue value) {
		SignValue sval = (SignValue) value;
		
		// incompatible domain system
		if (sval == null)
			return false;
		
		if (m_value == Sign.EMPTY)
			return true;
		
		if (m_value == sval.getValue())
			return true;
		
		if (sval.getValue() == Sign.PLUSMINUS)
			return true;
		
		return false;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#copy()
	 */
	@Override
	public SignValue copy() {
		return new SignValue(m_value);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#add(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue add(IAbstractValue value) {
		SignValue sval = (SignValue) value;
		
		if (sval == null) return new SignValue(Sign.EMPTY);
		
		Sign otherSign = sval.getValue();
		
		switch (m_value) {
		case ZERO :
			return new SignValue(otherSign);
		case PLUS :
			switch (otherSign) {
			case ZERO :
			case PLUS :
				return new SignValue(Sign.PLUS);
			case MINUS :
			case PLUSMINUS :
				return new SignValue(Sign.PLUSMINUS);
			default :
				return new SignValue(Sign.EMPTY);
			}
		case MINUS :
			switch (otherSign) {
			case ZERO :
			case MINUS :
				return new SignValue(Sign.MINUS);
			case PLUS :
			case PLUSMINUS :
				return new SignValue(Sign.PLUSMINUS);
			default :
				return new SignValue(Sign.EMPTY);
			}
		case PLUSMINUS :
			return new SignValue(Sign.PLUSMINUS);
		default :
			return new SignValue(Sign.EMPTY);
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#subtract(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue subtract(IAbstractValue value) {
		SignValue sval = (SignValue) value;
				
		if (sval == null) return new SignValue(Sign.EMPTY);
		
		Sign otherSign = sval.getValue();
		
		switch (m_value) {
		case ZERO :
			switch (otherSign) {
			case ZERO :
			case PLUSMINUS :
				return new SignValue(otherSign);
			case PLUS :
				return new SignValue(Sign.MINUS);
			case MINUS :
				return new SignValue(Sign.PLUS);
			default :
				return new SignValue(Sign.EMPTY);
			}
		case PLUS :
			switch (otherSign) {
			case ZERO :
			case MINUS :
				return new SignValue(Sign.PLUS);
			case PLUS :
			case PLUSMINUS :
				return new SignValue(Sign.PLUSMINUS);
			default :
				return new SignValue(Sign.EMPTY);
			}
		case MINUS :
			switch (otherSign) {
			case ZERO :
			case PLUS :
				return new SignValue(Sign.MINUS);
			case MINUS :
			case PLUSMINUS :
				return new SignValue(Sign.PLUSMINUS);
			default :
				return new SignValue(Sign.EMPTY);
			}
		case PLUSMINUS :
			return new SignValue(Sign.PLUSMINUS);
		default :
			return new SignValue(Sign.EMPTY);
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#multiply(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue multiply(IAbstractValue value) {
		SignValue sval = (SignValue) value;
		
		if (sval == null) return new SignValue(Sign.EMPTY);
		
		Sign otherSign = sval.getValue();
		
		switch (m_value) {
		case ZERO :
			return new SignValue(Sign.ZERO);
		case PLUS :
			switch (otherSign) {
			case ZERO :
				return new SignValue(Sign.ZERO);
			case PLUS :
				return new SignValue(Sign.PLUS);
			case MINUS :
				return new SignValue(Sign.MINUS);
			case PLUSMINUS :
				return new SignValue(Sign.PLUSMINUS);
			default :
				return new SignValue(Sign.EMPTY);
			}
		case MINUS :
			switch (otherSign) {
			case ZERO :
				return new SignValue(Sign.ZERO);
			case PLUS :
				return new SignValue(Sign.MINUS);
			case MINUS :
				return new SignValue(Sign.PLUS);
			case PLUSMINUS :
				return new SignValue(Sign.PLUSMINUS);
			default :
				return new SignValue(Sign.EMPTY);
			}
		case PLUSMINUS :
			return new SignValue(Sign.PLUSMINUS);
		default :
			return new SignValue(Sign.EMPTY);
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#divide(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue divide(IAbstractValue value) {
		SignValue sval = (SignValue) value;

		if (sval == null) return new SignValue(Sign.EMPTY);
		
		if ((sval.getValue() == Sign.ZERO) || (sval.getValue() == Sign.PLUSMINUS)) {
			AbstractInterpreter.getLogger().warn(String.format("Potential division by zero: %s / %s", this, sval));
			return new SignValue(Sign.EMPTY);
		}
		
		return this.multiply(value);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#modulo(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue modulo(IAbstractValue value) {
		SignValue sval = (SignValue) value;

		if (sval == null) return new SignValue(Sign.EMPTY);

		if ((sval.getValue() == Sign.ZERO) || (sval.getValue() == Sign.PLUSMINUS)) {
			AbstractInterpreter.getLogger().warn(String.format("Potential modulo division by zero: %s %% %s", this, sval));
			return new SignValue(Sign.EMPTY);
		}
		
		return new SignValue(Sign.PLUS); // remainder is always >= 0
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#negation()
	 */
	@Override
	public SignValue negative() {
		switch (m_value) {
		case PLUS :
			return new SignValue(Sign.MINUS);
		case MINUS :
			return new SignValue(Sign.PLUS);
		default :
			return new SignValue(m_value);
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue compareIsEqual(IAbstractValue value) {
		SignValue sval = (SignValue) value;

		if (sval == null) return new SignValue(Sign.EMPTY);
		
		Sign otherSign = sval.getValue();
		
		if (m_value == otherSign)
			return new SignValue(m_value);
		
		switch (m_value) {
		case ZERO :
			switch (otherSign) {
			case ZERO :
			case PLUSMINUS :
				return new SignValue(Sign.ZERO);
			case MINUS :
			case PLUS :
			default :
				return new SignValue(Sign.EMPTY);
			}
		case PLUS :
			switch (otherSign) {
			case PLUS :
			case PLUSMINUS :
				return new SignValue(Sign.PLUS);
			case ZERO :
			case MINUS :
			default :
				return new SignValue(Sign.EMPTY);
			}
		case MINUS :
			switch (otherSign) {
			case MINUS :
			case PLUSMINUS :
				return new SignValue(Sign.MINUS);
			case ZERO :
			case PLUS :
			default :
				return new SignValue(Sign.EMPTY);
			}
		case PLUSMINUS :
			return new SignValue(otherSign);
		default :
			return new SignValue(Sign.EMPTY);
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsNotEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue compareIsNotEqual(IAbstractValue value) {
		SignValue sval = (SignValue) value;

		if (sval == null) return new SignValue(Sign.EMPTY);
		
		Sign otherSign = sval.getValue();
		
		switch (m_value) {
		case ZERO :
			switch (otherSign) {
			case ZERO :
				return new SignValue(Sign.EMPTY);
			default :
				return new SignValue(otherSign);
			}
		case PLUS :
			switch (otherSign) {
			case PLUS :
				return new SignValue(Sign.PLUS);
			case ZERO :
			case MINUS :
			case PLUSMINUS :
				return new SignValue(Sign.PLUSMINUS);
			default :
				return new SignValue(Sign.EMPTY);
			}
		case MINUS :
			switch (otherSign) {
			case MINUS :
				return new SignValue(Sign.MINUS);
			case PLUS :
			case ZERO :
			case PLUSMINUS :
				return new SignValue(Sign.PLUSMINUS);
			default :
				return new SignValue(Sign.EMPTY);
			}
		case PLUSMINUS :
			return new SignValue(Sign.PLUSMINUS);
		default :
			return new SignValue(Sign.EMPTY);
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsLess(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue compareIsLess(IAbstractValue value) {
		SignValue sval = (SignValue) value;

		if (sval == null) return new SignValue(Sign.EMPTY);
		
		Sign otherSign = sval.getValue();
		
		switch (m_value) {
		case ZERO :
			switch (otherSign) {
			case PLUS :
			case PLUSMINUS :
				return new SignValue(Sign.ZERO);
			case ZERO :
			case MINUS :
			default :
				return new SignValue(Sign.EMPTY);
			}
		case PLUS :
			switch (otherSign) {
			case PLUS :
			case PLUSMINUS :
				return new SignValue(Sign.PLUS);
			case ZERO :
			case MINUS :
			default :
				return new SignValue(Sign.EMPTY);
			}
		case MINUS :
			return new SignValue((otherSign == Sign.EMPTY) ? Sign.EMPTY : Sign.MINUS);
		case PLUSMINUS :
			switch (otherSign) {
			case ZERO :
			case MINUS :
				return new SignValue(Sign.MINUS);
			case PLUS :
			case PLUSMINUS :
				return new SignValue(Sign.PLUSMINUS);
			default :
				return new SignValue(Sign.EMPTY);
			}
		default :
			return new SignValue(Sign.EMPTY);
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsGreater(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue compareIsGreater(IAbstractValue value) {
		SignValue sval = (SignValue) value;

		if (sval == null) return new SignValue(Sign.EMPTY);
		
		Sign otherSign = sval.getValue();
		
		switch (m_value) {
		case ZERO :
			switch (otherSign) {
			case MINUS :
			case PLUSMINUS :
				return new SignValue(Sign.ZERO);
			case ZERO :
			case PLUS :
			default :
				return new SignValue(Sign.EMPTY);
			}
		case PLUS :
			return new SignValue((otherSign == Sign.EMPTY) ? Sign.EMPTY : Sign.PLUS);
		case MINUS :
			switch (otherSign) {
			case MINUS :
			case PLUSMINUS :
				return new SignValue(Sign.MINUS);
			case ZERO :
			case PLUS :
			default :
				return new SignValue(Sign.EMPTY);
			}
		case PLUSMINUS :
			switch (otherSign) {
			case ZERO :
			case PLUS :
				return new SignValue(Sign.PLUS);
			case MINUS :
			case PLUSMINUS :
				return new SignValue(Sign.PLUSMINUS);
			default :
				return new SignValue(Sign.EMPTY);
			}
		default :
			return new SignValue(Sign.EMPTY);
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsLessEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue compareIsLessEqual(IAbstractValue value) {
		SignValue sval = (SignValue) value;

		if (sval == null) return new SignValue(Sign.EMPTY);
		
		Sign otherSign = sval.getValue();
		
		switch (m_value) {
		case ZERO :
			switch (otherSign) {
			case ZERO :
			case PLUS :
			case PLUSMINUS :
				return new SignValue(Sign.ZERO);
			case MINUS :
			default :
				return new SignValue(Sign.EMPTY);
			}
		case PLUS :
			switch (otherSign) {
			case PLUS :
			case PLUSMINUS :
				return new SignValue(Sign.PLUS);
			case ZERO :
			case MINUS :
			default :
				return new SignValue(Sign.EMPTY);
			}
		case MINUS :
			return new SignValue((otherSign == Sign.EMPTY) ? Sign.EMPTY : Sign.MINUS);
		case PLUSMINUS :
			switch (otherSign) {
			case ZERO :
			case MINUS :
				return new SignValue(Sign.MINUS);
			case PLUS :
			case PLUSMINUS :
				return new SignValue(Sign.PLUSMINUS);
			default :
				return new SignValue(Sign.EMPTY);
			}
		default :
			return new SignValue(Sign.EMPTY);
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsGreaterEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue compareIsGreaterEqual(IAbstractValue value) {
		SignValue sval = (SignValue) value;

		if (sval == null) return new SignValue(Sign.EMPTY);
		
		Sign otherSign = sval.getValue();
		
		switch (m_value) {
		case ZERO :
			switch (otherSign) {
			case ZERO :
			case MINUS :
			case PLUSMINUS :
				return new SignValue(Sign.ZERO);
			case PLUS :
			default :
				return new SignValue(Sign.EMPTY);
			}
		case PLUS :
			return new SignValue((otherSign == Sign.EMPTY) ? Sign.EMPTY : Sign.PLUS);
		case MINUS :
			switch (otherSign) {
			case MINUS :
			case PLUSMINUS :
				return new SignValue(Sign.MINUS);
			case ZERO :
			case PLUS :
			default :
				return new SignValue(Sign.EMPTY);
			}
		case PLUSMINUS :
			switch (otherSign) {
			case ZERO :
			case PLUS :
				return new SignValue(Sign.PLUS);
			case MINUS :
			case PLUSMINUS :
				return new SignValue(Sign.PLUSMINUS);
			default :
				return new SignValue(Sign.EMPTY);
			}
		default :
			return new SignValue(Sign.EMPTY);
		}
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
}
