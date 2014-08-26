/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.booldomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;

/**
 * @author Christopher Dillo
 *
 */
public class BoolValue implements IAbstractValue<BoolValue.Bool> {
	
	/**
	 * Possible values for the bool domain.
	 * EMPTY < TRUE, FALSE < UNKNOWN
	 * TRUE, FALSE : no relation
	 */
	public enum Bool {
		EMPTY, TRUE, FALSE, UNKNOWN
	}

	private Bool m_value;
	
	private BoolDomainFactory m_factory;
	
	private Logger m_logger;
	
	/**
	 * Generate a new BoolValue with the given value
	 * @param value TRUE? UNKNOWN?
	 */
	protected BoolValue(Bool value, BoolDomainFactory factory, Logger logger) {
		m_value = value;
		m_factory = factory;
		m_logger = logger;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#getValue()
	 */
	public Bool getValue() {
		return m_value;
	}
	
	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#isTop()
	 */
	@Override
	public boolean isTop() {
		return m_value == Bool.UNKNOWN;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#isBottom()
	 */
	@Override
	public boolean isBottom() {
		return m_value == Bool.EMPTY;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#representsSingleConcreteValue()
	 */
	@Override
	public boolean representsSingleConcreteValue() {
		return (m_value == Bool.TRUE) || (m_value == Bool.FALSE);
	}
	
	/**
	 * @return True iff the value is FALSE or EMPTY
	 */
	public boolean isFalse() {
		return m_value == Bool.FALSE;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#isEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean isEqual(IAbstractValue<?> value) {
		BoolValue val = (BoolValue) value;
		if (val == null) return false;
		
		return (m_value == val.getValue());
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#isSuper(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean isSuper(IAbstractValue<?> value) {
		BoolValue val = (BoolValue) value;
		if (val == null) return false;
		
		if (val.getValue() == Bool.EMPTY) return true; 
		
		if (m_value == Bool.UNKNOWN) return true;
		
		if (m_value == val.getValue()) return true;
		
		return false;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#isSub(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean isSub(IAbstractValue<?> value) {
		BoolValue val = (BoolValue) value;
		if (val == null) return false;
		
		if (val.getValue() == Bool.UNKNOWN) return true; 
		
		if (m_value == Bool.EMPTY) return true;
		
		if (m_value == val.getValue()) return true;
		
		return false;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#copy()
	 */
	@Override
	public BoolValue copy() {
		return m_factory.makeValue(m_value);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#add(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue add(IAbstractValue<?> value) {
		m_logger.debug("Invalid operation ADD on BoolValue");
		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#subtract(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue subtract(IAbstractValue<?> value) {
		m_logger.debug("Invalid operation SUBTRACT on BoolValue");
		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#multiply(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue multiply(IAbstractValue<?> value) {
		m_logger.debug("Invalid operation MULTIPLY on BoolValue");
		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#divide(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue divide(IAbstractValue<?> value) {
		m_logger.debug("Invalid operation DIVIDE on BoolValue");
		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#modulo(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue modulo(IAbstractValue<?> value) {
		m_logger.debug("Invalid operation MODULO on BoolValue");
		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#negative()
	 */
	@Override
	public BoolValue negative() {
		m_logger.debug("Invalid operation NEGATIVE on BoolValue");
		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue compareIsEqual(IAbstractValue<?> value) {
		BoolValue boolVal = booleanFromAbstractValue(value);
		if (boolVal == null) return m_factory.makeBottomValue();
		Bool bool = boolVal.getValue();
		
		switch (m_value) {
		case TRUE :
			switch (bool) {
			case TRUE :
			case UNKNOWN :
				return m_factory.makeValue(Bool.TRUE);
			default :
				return m_factory.makeBottomValue();
			}
		case FALSE :
			switch (bool) {
			case FALSE :
			case UNKNOWN :
				return m_factory.makeValue(Bool.FALSE);
			default :
				return m_factory.makeBottomValue();
			}
		case UNKNOWN :
			switch (bool) {
			case TRUE :
				return m_factory.makeValue(Bool.TRUE);
			case FALSE :
				return m_factory.makeValue(Bool.FALSE);
			case UNKNOWN :
				return m_factory.makeValue(Bool.UNKNOWN);
			default :
				return m_factory.makeBottomValue();
			}
		case EMPTY :
		default :
			return m_factory.makeBottomValue();
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsNotEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue compareIsNotEqual(IAbstractValue<?> value) {
		BoolValue boolVal = booleanFromAbstractValue(value);
		if (boolVal == null) return m_factory.makeBottomValue();
		Bool bool = boolVal.getValue();
		
		switch (m_value) {
		case TRUE :
			switch (bool) {
			case FALSE :
			case UNKNOWN :
				return m_factory.makeValue(Bool.TRUE);
			default :
				return m_factory.makeBottomValue();
			}
		case FALSE :
			switch (bool) {
			case TRUE :
			case UNKNOWN :
				return m_factory.makeValue(Bool.FALSE);
			default :
				return m_factory.makeBottomValue();
			}
		case UNKNOWN :
			switch (bool) {
			case TRUE :
				return m_factory.makeValue(Bool.FALSE);
			case FALSE :
				return m_factory.makeValue(Bool.TRUE);
			case UNKNOWN :
				return m_factory.makeValue(Bool.UNKNOWN);
			default :
				return m_factory.makeBottomValue();
			}
		case EMPTY :
		default :
			return m_factory.makeBottomValue();
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsLess(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue compareIsLess(IAbstractValue<?> value) {
		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsGreater(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue compareIsGreater(IAbstractValue<?> value) {
		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsLessEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue compareIsLessEqual(IAbstractValue<?> value) {
		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsGreaterEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue compareIsGreaterEqual(IAbstractValue<?> value) {
		return m_factory.makeBottomValue();
	}
	
	/**
	 * @param value The value to operate with (this <-> value)
	 * @return A BoolValue representing the result of the operation
	 */
	public BoolValue logicIff(IAbstractValue<?> value) {
		BoolValue boolVal = booleanFromAbstractValue(value);
		if (boolVal == null) return m_factory.makeBottomValue();
		Bool bool = boolVal.getValue();
		
		switch (m_value) {
		case TRUE :
			switch (bool) {
			case TRUE :
				return m_factory.makeValue(Bool.TRUE);
			case FALSE :
				return m_factory.makeValue(Bool.FALSE);
			case UNKNOWN :
				return m_factory.makeValue(Bool.UNKNOWN);
			default :
				return m_factory.makeBottomValue();
			}
		case FALSE :
			switch (bool) {
			case TRUE :
				return m_factory.makeValue(Bool.FALSE);
			case FALSE :
				return m_factory.makeValue(Bool.TRUE);
			case UNKNOWN :
				return m_factory.makeValue(Bool.UNKNOWN);
			default :
				return m_factory.makeBottomValue();
			}
		case UNKNOWN :
			switch (bool) {
			case TRUE :
			case FALSE :
			case UNKNOWN :
				return m_factory.makeValue(Bool.UNKNOWN);
			default :
				return m_factory.makeBottomValue();
			}
		case EMPTY :
		default :
			return m_factory.makeBottomValue();
		}
	}

	/**
	 * @param value The value to operate with (this -> value)
	 * @return A BoolValue representing the result of the operation
	 */
	public BoolValue logicImplies(IAbstractValue<?> value) {
		BoolValue boolVal = booleanFromAbstractValue(value);
		if (boolVal == null) return m_factory.makeBottomValue();
		Bool bool = boolVal.getValue();
		
		switch (m_value) {
		case TRUE :
			switch (bool) {
			case TRUE :
				return m_factory.makeValue(Bool.TRUE);
			case FALSE :
				return m_factory.makeValue(Bool.FALSE);
			case UNKNOWN :
				return m_factory.makeValue(Bool.UNKNOWN);
			default :
				return m_factory.makeBottomValue();
			}
		case FALSE :
			switch (bool) {
			case TRUE :
			case FALSE :
			case UNKNOWN :
				return m_factory.makeValue(Bool.TRUE);
			default :
				return m_factory.makeBottomValue();
			}
		case UNKNOWN :
			switch (bool) {
			case TRUE :
				return m_factory.makeValue(Bool.TRUE);
			case FALSE :
			case UNKNOWN :
				return m_factory.makeValue(Bool.UNKNOWN);
			default :
				return m_factory.makeBottomValue();
			}
		case EMPTY :
		default :
			return m_factory.makeBottomValue();
		}
	}

	/**
	 * @param value The value to operate with (this && value)
	 * @return A BoolValue representing the result of the operation
	 */
	public BoolValue logicAnd(IAbstractValue<?> value) {
		BoolValue boolVal = booleanFromAbstractValue(value);
		if (boolVal == null) return m_factory.makeBottomValue();
		Bool bool = boolVal.getValue();
		
		switch (m_value) {
		case TRUE :
			switch (bool) {
			case TRUE :
				return m_factory.makeValue(Bool.TRUE);
			case FALSE :
				return m_factory.makeValue(Bool.FALSE);
			case UNKNOWN :
				return m_factory.makeValue(Bool.UNKNOWN);
			default :
				return m_factory.makeBottomValue();
			}
		case FALSE :
			switch (bool) {
			case TRUE :
			case FALSE :
			case UNKNOWN :
				return m_factory.makeValue(Bool.FALSE);
			default :
				return m_factory.makeBottomValue();
			}
		case UNKNOWN :
			switch (bool) {
			case FALSE :
				return m_factory.makeValue(Bool.FALSE);
			case TRUE :
			case UNKNOWN :
				return m_factory.makeValue(Bool.UNKNOWN);
			default :
				return m_factory.makeBottomValue();
			}
		case EMPTY :
		default :
			return m_factory.makeBottomValue();
		}
	}

	/**
	 * @param value The value to operate with (this || value)
	 * @return A BoolValue representing the result of the operation
	 */
	public BoolValue logicOr(IAbstractValue<?> value) {
		BoolValue boolVal = booleanFromAbstractValue(value);
		if (boolVal == null) return m_factory.makeBottomValue();
		Bool bool = boolVal.getValue();
		
		switch (m_value) {
		case TRUE :
			switch (bool) {
			case TRUE :
			case FALSE :
			case UNKNOWN :
				return m_factory.makeValue(Bool.TRUE);
			default :
				return m_factory.makeBottomValue();
			}
		case FALSE :
			switch (bool) {
			case TRUE :
				return m_factory.makeValue(Bool.TRUE);
			case FALSE :
				return m_factory.makeValue(Bool.FALSE);
			case UNKNOWN :
				return m_factory.makeValue(Bool.UNKNOWN);
			default :
				return m_factory.makeBottomValue();
			}
		case UNKNOWN :
			switch (bool) {
			case TRUE :
				return m_factory.makeValue(Bool.TRUE);
			case FALSE :
			case UNKNOWN :
				return m_factory.makeValue(Bool.UNKNOWN);
			default :
				return m_factory.makeBottomValue();
			}
		case EMPTY :
		default :
			return m_factory.makeBottomValue();
		}
	}

	/**
	 * @return A BoolValue representing the result of the operation: not value
	 */
	public BoolValue logicNot() {
		switch (m_value) {
		case TRUE :
			return m_factory.makeValue(Bool.FALSE);
		case FALSE :
			return m_factory.makeValue(Bool.TRUE);
		case UNKNOWN :
			return m_factory.makeValue(Bool.UNKNOWN);
		case EMPTY :
		default :
			return m_factory.makeBottomValue();
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#bitVectorConcat(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue bitVectorConcat(IAbstractValue<?> value) {
		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#bitVectorAccess(int, int)
	 */
	@Override
	public BoolValue bitVectorAccess(int start, int end) {
		return m_factory.makeBottomValue();
	}
	
	/**
	 * Used to compare bool with not-bool, treating not-bool as false iff it is not-bool.bottom
	 * @param value
	 * @return
	 */
	private BoolValue booleanFromAbstractValue(IAbstractValue<?> value) {
		if (value == null)
			return null;
		
		if (value instanceof BoolValue) {
			if (value.isBottom())
				return m_factory.makeBoolValue(false);
			return (BoolValue) value;
		}
		
		return m_factory.makeBoolValue(!value.isBottom());
	}

	@Override
	public String toString() {
		switch (m_value) {
		case TRUE :
			return "TRUE";
		case FALSE :
			return "FALSE";
		case UNKNOWN :
			return "UNKNOWN";
		case EMPTY :
		default :
			return "EMPTY";
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
