/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.booldomain;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;

/**
 * @author Christopher Dillo
 *
 */
public class BoolValue implements IAbstractValue {
	
	/**
	 * Possible values for the bool domain.
	 * EMPTY < TRUE, FALSE < UNKNOWN
	 * TRUE, FALSE : no relation
	 */
	enum Bool {
		EMPTY, TRUE, FALSE, UNKNOWN
	}

	private Bool m_value;

	
	/**
	 * Generate a new BoolValue with the given value
	 * @param value TRUE? UNKNOWN?
	 */
	public BoolValue(Bool value) {
		m_value = value;
	}
	
	public Bool getValue() {
		return m_value;
	}
	
	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#getDomainID()
	 */
	@Override
	public String getDomainID() {
		return BoolDomainFactory.s_DomainID;
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
	public boolean isEqual(IAbstractValue value) {
		BoolValue val = (BoolValue) value;
		if (val == null) return false;
		
		return (m_value == val.getValue());
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#isSuper(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean isSuper(IAbstractValue value) {
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
	public boolean isSub(IAbstractValue value) {
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
		return new BoolValue(m_value);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#add(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue add(IAbstractValue value) {
		return new BoolValue(Bool.EMPTY);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#subtract(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue subtract(IAbstractValue value) {
		return new BoolValue(Bool.EMPTY);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#multiply(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue multiply(IAbstractValue value) {
		return new BoolValue(Bool.EMPTY);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#divide(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue divide(IAbstractValue value) {
		return new BoolValue(Bool.EMPTY);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#modulo(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue modulo(IAbstractValue value) {
		return new BoolValue(Bool.EMPTY);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#negative()
	 */
	@Override
	public BoolValue negative() {
		return new BoolValue(Bool.EMPTY);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue compareIsEqual(IAbstractValue value) {
		BoolValue bval = (BoolValue) value;
		
		if (bval == null) return new BoolValue(Bool.EMPTY);
		
		Bool bool = bval.getValue();
		switch (m_value) {
		case TRUE :
			switch (bool) {
			case TRUE :
			case UNKNOWN :
				return new BoolValue(Bool.TRUE);
			default :
				return new BoolValue(Bool.EMPTY);
			}
		case FALSE :
			switch (bool) {
			case FALSE :
			case UNKNOWN :
				return new BoolValue(Bool.FALSE);
			default :
				return new BoolValue(Bool.EMPTY);
			}
		case UNKNOWN :
			switch (bool) {
			case TRUE :
				return new BoolValue(Bool.TRUE);
			case FALSE :
				return new BoolValue(Bool.FALSE);
			case UNKNOWN :
				return new BoolValue(Bool.UNKNOWN);
			default :
				return new BoolValue(Bool.EMPTY);
			}
		case EMPTY :
		default :
			return new BoolValue(Bool.EMPTY);
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsNotEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue compareIsNotEqual(IAbstractValue value) {
		BoolValue bval = (BoolValue) value;
		
		if (bval == null) return new BoolValue(Bool.EMPTY);
		
		Bool bool = bval.getValue();
		switch (m_value) {
		case TRUE :
			switch (bool) {
			case FALSE :
			case UNKNOWN :
				return new BoolValue(Bool.TRUE);
			default :
				return new BoolValue(Bool.EMPTY);
			}
		case FALSE :
			switch (bool) {
			case TRUE :
			case UNKNOWN :
				return new BoolValue(Bool.FALSE);
			default :
				return new BoolValue(Bool.EMPTY);
			}
		case UNKNOWN :
			switch (bool) {
			case TRUE :
				return new BoolValue(Bool.FALSE);
			case FALSE :
				return new BoolValue(Bool.TRUE);
			case UNKNOWN :
				return new BoolValue(Bool.UNKNOWN);
			default :
				return new BoolValue(Bool.EMPTY);
			}
		case EMPTY :
		default :
			return new BoolValue(Bool.EMPTY);
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsLess(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue compareIsLess(IAbstractValue value) {
		return new BoolValue(Bool.EMPTY);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsGreater(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue compareIsGreater(IAbstractValue value) {
		return new BoolValue(Bool.EMPTY);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsLessEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue compareIsLessEqual(IAbstractValue value) {
		return new BoolValue(Bool.EMPTY);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue#compareIsGreaterEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue compareIsGreaterEqual(IAbstractValue value) {
		return new BoolValue(Bool.EMPTY);
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
		if (value == null) return new BoolValue(Bool.EMPTY);
		
		Bool bool = value.getValue();
		switch (m_value) {
		case TRUE :
			switch (bool) {
			case TRUE :
				return new BoolValue(Bool.TRUE);
			case FALSE :
				return new BoolValue(Bool.FALSE);
			case UNKNOWN :
				return new BoolValue(Bool.UNKNOWN);
			default :
				return new BoolValue(Bool.EMPTY);
			}
		case FALSE :
			switch (bool) {
			case TRUE :
				return new BoolValue(Bool.FALSE);
			case FALSE :
				return new BoolValue(Bool.TRUE);
			case UNKNOWN :
				return new BoolValue(Bool.UNKNOWN);
			default :
				return new BoolValue(Bool.EMPTY);
			}
		case UNKNOWN :
			switch (bool) {
			case TRUE :
			case FALSE :
			case UNKNOWN :
				return new BoolValue(Bool.UNKNOWN);
			default :
				return new BoolValue(Bool.EMPTY);
			}
		case EMPTY :
		default :
			return new BoolValue(Bool.EMPTY);
		}
	}

	/**
	 * @param value The value to operate with (this -> value)
	 * @return A BoolValue representing the result of the operation
	 */
	public BoolValue logicImplies(BoolValue value) {
		if (value == null) return new BoolValue(Bool.EMPTY);
		
		Bool bool = value.getValue();
		switch (m_value) {
		case TRUE :
			switch (bool) {
			case TRUE :
				return new BoolValue(Bool.TRUE);
			case FALSE :
				return new BoolValue(Bool.FALSE);
			case UNKNOWN :
				return new BoolValue(Bool.UNKNOWN);
			default :
				return new BoolValue(Bool.EMPTY);
			}
		case FALSE :
			switch (bool) {
			case TRUE :
			case FALSE :
			case UNKNOWN :
				return new BoolValue(Bool.TRUE);
			default :
				return new BoolValue(Bool.EMPTY);
			}
		case UNKNOWN :
			switch (bool) {
			case TRUE :
				return new BoolValue(Bool.TRUE);
			case FALSE :
			case UNKNOWN :
				return new BoolValue(Bool.UNKNOWN);
			default :
				return new BoolValue(Bool.EMPTY);
			}
		case EMPTY :
		default :
			return new BoolValue(Bool.EMPTY);
		}
	}

	/**
	 * @param value The value to operate with (this && value)
	 * @return A BoolValue representing the result of the operation
	 */
	public BoolValue logicAnd(BoolValue value) {
		if (value == null) return new BoolValue(Bool.EMPTY);
		
		Bool bool = value.getValue();
		switch (m_value) {
		case TRUE :
			switch (bool) {
			case TRUE :
				return new BoolValue(Bool.TRUE);
			case FALSE :
				return new BoolValue(Bool.FALSE);
			case UNKNOWN :
				return new BoolValue(Bool.UNKNOWN);
			default :
				return new BoolValue(Bool.EMPTY);
			}
		case FALSE :
			switch (bool) {
			case TRUE :
			case FALSE :
			case UNKNOWN :
				return new BoolValue(Bool.FALSE);
			default :
				return new BoolValue(Bool.EMPTY);
			}
		case UNKNOWN :
			switch (bool) {
			case FALSE :
				return new BoolValue(Bool.FALSE);
			case TRUE :
			case UNKNOWN :
				return new BoolValue(Bool.UNKNOWN);
			default :
				return new BoolValue(Bool.EMPTY);
			}
		case EMPTY :
		default :
			return new BoolValue(Bool.EMPTY);
		}
	}

	/**
	 * @param value The value to operate with (this || value)
	 * @return A BoolValue representing the result of the operation
	 */
	public BoolValue logicOr(BoolValue value) {
		if (value == null) return new BoolValue(Bool.EMPTY);
		
		Bool bool = value.getValue();
		switch (m_value) {
		case TRUE :
			switch (bool) {
			case TRUE :
			case FALSE :
			case UNKNOWN :
				return new BoolValue(Bool.TRUE);
			default :
				return new BoolValue(Bool.EMPTY);
			}
		case FALSE :
			switch (bool) {
			case TRUE :
				return new BoolValue(Bool.TRUE);
			case FALSE :
				return new BoolValue(Bool.FALSE);
			case UNKNOWN :
				return new BoolValue(Bool.UNKNOWN);
			default :
				return new BoolValue(Bool.EMPTY);
			}
		case UNKNOWN :
			switch (bool) {
			case TRUE :
				return new BoolValue(Bool.TRUE);
			case FALSE :
			case UNKNOWN :
				return new BoolValue(Bool.UNKNOWN);
			default :
				return new BoolValue(Bool.EMPTY);
			}
		case EMPTY :
		default :
			return new BoolValue(Bool.EMPTY);
		}
	}

	/**
	 * @return A BoolValue representing the result of the operation: not value
	 */
	public BoolValue logicNot() {
		switch (m_value) {
		case TRUE :
			return new BoolValue(Bool.FALSE);
		case FALSE :
			return new BoolValue(Bool.TRUE);
		case UNKNOWN :
			return new BoolValue(Bool.UNKNOWN);
		case EMPTY :
		default :
			return new BoolValue(Bool.EMPTY);
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
