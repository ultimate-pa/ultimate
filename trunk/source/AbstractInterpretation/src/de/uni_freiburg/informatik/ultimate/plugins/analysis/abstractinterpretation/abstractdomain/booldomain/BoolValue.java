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
	enum Bool {
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
		return m_factory.makeValue(Bool.EMPTY);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#subtract(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue subtract(IAbstractValue<?> value) {
		m_logger.debug("Invalid operation SUBTRACT on BoolValue");
		return m_factory.makeValue(Bool.EMPTY);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#multiply(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue multiply(IAbstractValue<?> value) {
		m_logger.debug("Invalid operation MULTIPLY on BoolValue");
		return m_factory.makeValue(Bool.EMPTY);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#divide(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue divide(IAbstractValue<?> value) {
		m_logger.debug("Invalid operation DIVIDE on BoolValue");
		return m_factory.makeValue(Bool.EMPTY);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#modulo(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue modulo(IAbstractValue<?> value) {
		m_logger.debug("Invalid operation MODULO on BoolValue");
		return m_factory.makeValue(Bool.EMPTY);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#negative()
	 */
	@Override
	public BoolValue negative() {
		m_logger.debug("Invalid operation NEGATIVE on BoolValue");
		return m_factory.makeValue(Bool.EMPTY);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue compareIsEqual(IAbstractValue<?> value) {
		Bool bool = (Bool) value.getValue();
		if (bool == null) return m_factory.makeValue(Bool.EMPTY);
		
		switch (m_value) {
		case TRUE :
			switch (bool) {
			case TRUE :
			case UNKNOWN :
				return m_factory.makeValue(Bool.TRUE);
			default :
				return m_factory.makeValue(Bool.EMPTY);
			}
		case FALSE :
			switch (bool) {
			case FALSE :
			case UNKNOWN :
				return m_factory.makeValue(Bool.FALSE);
			default :
				return m_factory.makeValue(Bool.EMPTY);
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
				return m_factory.makeValue(Bool.EMPTY);
			}
		case EMPTY :
		default :
			return m_factory.makeValue(Bool.EMPTY);
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsNotEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue compareIsNotEqual(IAbstractValue<?> value) {
		Bool bool = (Bool) value.getValue();
		if (bool == null) return m_factory.makeValue(Bool.EMPTY);
		
		switch (m_value) {
		case TRUE :
			switch (bool) {
			case FALSE :
			case UNKNOWN :
				return m_factory.makeValue(Bool.TRUE);
			default :
				return m_factory.makeValue(Bool.EMPTY);
			}
		case FALSE :
			switch (bool) {
			case TRUE :
			case UNKNOWN :
				return m_factory.makeValue(Bool.FALSE);
			default :
				return m_factory.makeValue(Bool.EMPTY);
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
				return m_factory.makeValue(Bool.EMPTY);
			}
		case EMPTY :
		default :
			return m_factory.makeValue(Bool.EMPTY);
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsLess(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue compareIsLess(IAbstractValue<?> value) {
		return m_factory.makeValue(Bool.EMPTY);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsGreater(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue compareIsGreater(IAbstractValue<?> value) {
		return m_factory.makeValue(Bool.EMPTY);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsLessEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue compareIsLessEqual(IAbstractValue<?> value) {
		return m_factory.makeValue(Bool.EMPTY);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsGreaterEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue compareIsGreaterEqual(IAbstractValue<?> value) {
		return m_factory.makeValue(Bool.EMPTY);
	}
	
	/*
		case LOGICIFF :
		case LOGICIMPLIES :
		case LOGICAND :
		case LOGICOR :
	*/


	/**
	 * @param value The value to operate with (this <-> value)
	 * @return A BoolValue representing the result of the operation
	 */
	public BoolValue logicIff(BoolValue value) {
		if (value == null) return m_factory.makeValue(Bool.EMPTY);
		
		Bool bool = value.getValue();
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
				return m_factory.makeValue(Bool.EMPTY);
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
				return m_factory.makeValue(Bool.EMPTY);
			}
		case UNKNOWN :
			switch (bool) {
			case TRUE :
			case FALSE :
			case UNKNOWN :
				return m_factory.makeValue(Bool.UNKNOWN);
			default :
				return m_factory.makeValue(Bool.EMPTY);
			}
		case EMPTY :
		default :
			return m_factory.makeValue(Bool.EMPTY);
		}
	}

	/**
	 * @param value The value to operate with (this -> value)
	 * @return A BoolValue representing the result of the operation
	 */
	public BoolValue logicImplies(BoolValue value) {
		if (value == null) return m_factory.makeValue(Bool.EMPTY);
		
		Bool bool = value.getValue();
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
				return m_factory.makeValue(Bool.EMPTY);
			}
		case FALSE :
			switch (bool) {
			case TRUE :
			case FALSE :
			case UNKNOWN :
				return m_factory.makeValue(Bool.TRUE);
			default :
				return m_factory.makeValue(Bool.EMPTY);
			}
		case UNKNOWN :
			switch (bool) {
			case TRUE :
				return m_factory.makeValue(Bool.TRUE);
			case FALSE :
			case UNKNOWN :
				return m_factory.makeValue(Bool.UNKNOWN);
			default :
				return m_factory.makeValue(Bool.EMPTY);
			}
		case EMPTY :
		default :
			return m_factory.makeValue(Bool.EMPTY);
		}
	}

	/**
	 * @param value The value to operate with (this && value)
	 * @return A BoolValue representing the result of the operation
	 */
	public BoolValue logicAnd(BoolValue value) {
		if (value == null) return m_factory.makeValue(Bool.EMPTY);
		
		Bool bool = value.getValue();
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
				return m_factory.makeValue(Bool.EMPTY);
			}
		case FALSE :
			switch (bool) {
			case TRUE :
			case FALSE :
			case UNKNOWN :
				return m_factory.makeValue(Bool.FALSE);
			default :
				return m_factory.makeValue(Bool.EMPTY);
			}
		case UNKNOWN :
			switch (bool) {
			case FALSE :
				return m_factory.makeValue(Bool.FALSE);
			case TRUE :
			case UNKNOWN :
				return m_factory.makeValue(Bool.UNKNOWN);
			default :
				return m_factory.makeValue(Bool.EMPTY);
			}
		case EMPTY :
		default :
			return m_factory.makeValue(Bool.EMPTY);
		}
	}

	/**
	 * @param value The value to operate with (this || value)
	 * @return A BoolValue representing the result of the operation
	 */
	public BoolValue logicOr(BoolValue value) {
		if (value == null) return m_factory.makeValue(Bool.EMPTY);
		
		Bool bool = value.getValue();
		switch (m_value) {
		case TRUE :
			switch (bool) {
			case TRUE :
			case FALSE :
			case UNKNOWN :
				return m_factory.makeValue(Bool.TRUE);
			default :
				return m_factory.makeValue(Bool.EMPTY);
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
				return m_factory.makeValue(Bool.EMPTY);
			}
		case UNKNOWN :
			switch (bool) {
			case TRUE :
				return m_factory.makeValue(Bool.TRUE);
			case FALSE :
			case UNKNOWN :
				return m_factory.makeValue(Bool.UNKNOWN);
			default :
				return m_factory.makeValue(Bool.EMPTY);
			}
		case EMPTY :
		default :
			return m_factory.makeValue(Bool.EMPTY);
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
			return m_factory.makeValue(Bool.EMPTY);
		}
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
}
