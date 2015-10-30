package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.booldomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IAbstractValueFactory;

/**
 * @author Christopher Dillo
 *
 */
public class BoolValue implements IAbstractValue<BoolValue.Bool> {

	/**
	 * Possible values for the bool domain. EMPTY < TRUE, FALSE < UNKNOWN TRUE,
	 * FALSE : no relation
	 */
	public enum Bool {
		EMPTY, TRUE, FALSE, UNKNOWN
	}

	/**
	 * The actual value of this
	 */
	private Bool mValue;

	/**
	 * The factory for creating values like this
	 */
	private BoolValueFactory mFactory;

	/**
	 * The logger is needed in the operations
	 */
	private Logger mLogger;

	/**
	 * Generate a new BoolValue with the given value
	 * 
	 * @param value
	 *            TRUE? UNKNOWN?
	 */
	protected BoolValue(Bool value, BoolValueFactory factory, Logger logger) {
		mValue = value;
		mFactory = factory;
		mLogger = logger;
	}

	@Override
	public IAbstractValueFactory<?> getFactory() {
		return mFactory;
	}

	@Override
	public boolean isTrue() {
		return mValue == Bool.TRUE;
	}

	/**
	 * @return True iff the value is FALSE or EMPTY
	 */
	public boolean isFalse() {
		return mValue == Bool.FALSE;
	}

	public Bool getValue() {
		return mValue;
	}

	@Override
	public boolean isTop() {
		return mValue == Bool.UNKNOWN;
	}

	@Override
	public boolean isBottom() {
		return mValue == Bool.EMPTY;
	}

	@Override
	public boolean representsSingleConcreteValue() {
		return (mValue == Bool.TRUE) || (mValue == Bool.FALSE);
	}

	@Override
	public boolean isEqual(IAbstractValue<?> value) {
		BoolValue val = (BoolValue) value;
		if (val == null)
			return false;

		return (mValue == val.getValue());
	}

	@Override
	public boolean isSuperOrEqual(IAbstractValue<?> value) {
		BoolValue val = (BoolValue) value;
		if (val == null)
			return false;

		if (val.getValue() == Bool.EMPTY)
			return true;

		if (mValue == Bool.UNKNOWN)
			return true;

		if (mValue == val.getValue())
			return true;

		return false;
	}

	@Override
	public boolean isSub(IAbstractValue<?> value) {
		BoolValue val = (BoolValue) value;
		if (val == null)
			return false;

		if (val.getValue() == Bool.UNKNOWN)
			return true;

		if (mValue == Bool.EMPTY)
			return true;

		if (mValue == val.getValue())
			return true;

		return false;
	}

	@Override
	public BoolValue copy() {
		return mFactory.makeValue(mValue);
	}

	@Override
	public BoolValue add(IAbstractValue<?> value) {
		mLogger.debug("Invalid operation ADD on BoolValue");
		return mFactory.makeBottomValue();
	}

	@Override
	public BoolValue subtract(IAbstractValue<?> value) {
		mLogger.debug("Invalid operation SUBTRACT on BoolValue");
		return mFactory.makeBottomValue();
	}

	@Override
	public BoolValue multiply(IAbstractValue<?> value) {
		mLogger.debug("Invalid operation MULTIPLY on BoolValue");
		return mFactory.makeBottomValue();
	}

	@Override
	public BoolValue divide(IAbstractValue<?> value) {
		mLogger.debug("Invalid operation DIVIDE on BoolValue");
		return mFactory.makeBottomValue();
	}

	@Override
	public BoolValue modulo(IAbstractValue<?> value) {
		mLogger.debug("Invalid operation MODULO on BoolValue");
		return mFactory.makeBottomValue();
	}

	@Override
	public BoolValue negative() {
		mLogger.debug("Invalid operation NEGATIVE on BoolValue");
		return mFactory.makeBottomValue();
	}

	@Override
	public BoolValue compareIsEqual(IAbstractValue<?> value) {
		BoolValue boolVal = booleanFromAbstractValue(value);
		if (boolVal == null)
			return mFactory.makeBottomValue();
		Bool bool = boolVal.getValue();

		switch (mValue) {
		case TRUE:
			switch (bool) {
			case TRUE:
			case UNKNOWN:
				return mFactory.makeValue(Bool.TRUE);
			default:
				return mFactory.makeBottomValue();
			}
		case FALSE:
			switch (bool) {
			case FALSE:
			case UNKNOWN:
				return mFactory.makeValue(Bool.FALSE);
			default:
				return mFactory.makeBottomValue();
			}
		case UNKNOWN:
			switch (bool) {
			case TRUE:
				return mFactory.makeValue(Bool.TRUE);
			case FALSE:
				return mFactory.makeValue(Bool.FALSE);
			case UNKNOWN:
				return mFactory.makeValue(Bool.UNKNOWN);
			default:
				return mFactory.makeBottomValue();
			}
		case EMPTY:
		default:
			return mFactory.makeBottomValue();
		}
	}

	@Override
	public BoolValue compareIsNotEqual(IAbstractValue<?> value) {
		BoolValue boolVal = booleanFromAbstractValue(value);
		if (boolVal == null)
			return mFactory.makeBottomValue();
		Bool bool = boolVal.getValue();

		switch (mValue) {
		case TRUE:
			switch (bool) {
			case FALSE:
			case UNKNOWN:
				return mFactory.makeValue(Bool.TRUE);
			default:
				return mFactory.makeBottomValue();
			}
		case FALSE:
			switch (bool) {
			case TRUE:
			case UNKNOWN:
				return mFactory.makeValue(Bool.FALSE);
			default:
				return mFactory.makeBottomValue();
			}
		case UNKNOWN:
			switch (bool) {
			case TRUE:
				return mFactory.makeValue(Bool.FALSE);
			case FALSE:
				return mFactory.makeValue(Bool.TRUE);
			case UNKNOWN:
				return mFactory.makeValue(Bool.UNKNOWN);
			default:
				return mFactory.makeBottomValue();
			}
		case EMPTY:
		default:
			return mFactory.makeBottomValue();
		}
	}

	@Override
	public BoolValue compareIsLess(IAbstractValue<?> value) {
		return null;
	}

	@Override
	public BoolValue compareIsGreater(IAbstractValue<?> value) {
		return null;
	}

	@Override
	public BoolValue compareIsLessEqual(IAbstractValue<?> value) {
		return null;
	}

	@Override
	public BoolValue compareIsGreaterEqual(IAbstractValue<?> value) {
		return null;
	}

	/**
	 * @param value
	 *            The value to operate with (this <-> value)
	 * @return A BoolValue representing the result of the operation
	 */
	public BoolValue logicIff(IAbstractValue<?> value) {
		BoolValue boolVal = booleanFromAbstractValue(value);
		if (boolVal == null)
			return mFactory.makeBottomValue();
		Bool bool = boolVal.getValue();

		switch (mValue) {
		case TRUE:
			switch (bool) {
			case TRUE:
				return mFactory.makeValue(Bool.TRUE);
			case FALSE:
				return mFactory.makeValue(Bool.FALSE);
			case UNKNOWN:
				return mFactory.makeValue(Bool.UNKNOWN);
			default:
				return mFactory.makeBottomValue();
			}
		case FALSE:
			switch (bool) {
			case TRUE:
				return mFactory.makeValue(Bool.FALSE);
			case FALSE:
				return mFactory.makeValue(Bool.TRUE);
			case UNKNOWN:
				return mFactory.makeValue(Bool.UNKNOWN);
			default:
				return mFactory.makeBottomValue();
			}
		case UNKNOWN:
			switch (bool) {
			case TRUE:
			case FALSE:
			case UNKNOWN:
				return mFactory.makeValue(Bool.UNKNOWN);
			default:
				return mFactory.makeBottomValue();
			}
		case EMPTY:
		default:
			return mFactory.makeBottomValue();
		}
	}

	/**
	 * @param value
	 *            The value to operate with (this -> value)
	 * @return A BoolValue representing the result of the operation
	 */
	public BoolValue logicImplies(IAbstractValue<?> value) {
		BoolValue boolVal = booleanFromAbstractValue(value);
		if (boolVal == null)
			return mFactory.makeBottomValue();
		Bool bool = boolVal.getValue();

		switch (mValue) {
		case TRUE:
			switch (bool) {
			case TRUE:
				return mFactory.makeValue(Bool.TRUE);
			case FALSE:
				return mFactory.makeValue(Bool.FALSE);
			case UNKNOWN:
				return mFactory.makeValue(Bool.UNKNOWN);
			default:
				return mFactory.makeBottomValue();
			}
		case FALSE:
			switch (bool) {
			case TRUE:
			case FALSE:
			case UNKNOWN:
				return mFactory.makeValue(Bool.TRUE);
			default:
				return mFactory.makeBottomValue();
			}
		case UNKNOWN:
			switch (bool) {
			case TRUE:
				return mFactory.makeValue(Bool.TRUE);
			case FALSE:
			case UNKNOWN:
				return mFactory.makeValue(Bool.UNKNOWN);
			default:
				return mFactory.makeBottomValue();
			}
		case EMPTY:
		default:
			return mFactory.makeBottomValue();
		}
	}

	/**
	 * @param value
	 *            The value to operate with (this && value)
	 * @return A BoolValue representing the result of the operation
	 */
	public BoolValue logicAnd(IAbstractValue<?> value) {
		BoolValue boolVal = booleanFromAbstractValue(value);
		if (boolVal == null)
			return mFactory.makeBottomValue();
		Bool bool = boolVal.getValue();

		switch (mValue) {
		case TRUE:
			switch (bool) {
			case TRUE:
				return mFactory.makeValue(Bool.TRUE);
			case FALSE:
				return mFactory.makeValue(Bool.FALSE);
			case UNKNOWN:
				return mFactory.makeValue(Bool.UNKNOWN);
			default:
				return mFactory.makeBottomValue();
			}
		case FALSE:
			switch (bool) {
			case TRUE:
			case FALSE:
			case UNKNOWN:
				return mFactory.makeValue(Bool.FALSE);
			default:
				return mFactory.makeBottomValue();
			}
		case UNKNOWN:
			switch (bool) {
			case FALSE:
				return mFactory.makeValue(Bool.FALSE);
			case TRUE:
			case UNKNOWN:
				return mFactory.makeValue(Bool.UNKNOWN);
			default:
				return mFactory.makeBottomValue();
			}
		case EMPTY:
		default:
			return mFactory.makeBottomValue();
		}
	}

	/**
	 * @param value
	 *            The value to operate with (this || value)
	 * @return A BoolValue representing the result of the operation
	 */
	public BoolValue logicOr(IAbstractValue<?> value) {
		BoolValue boolVal = booleanFromAbstractValue(value);
		if (boolVal == null)
			return mFactory.makeBottomValue();
		Bool bool = boolVal.getValue();

		switch (mValue) {
		case TRUE:
			switch (bool) {
			case TRUE:
			case FALSE:
			case UNKNOWN:
				return mFactory.makeValue(Bool.TRUE);
			default:
				return mFactory.makeBottomValue();
			}
		case FALSE:
			switch (bool) {
			case TRUE:
				return mFactory.makeValue(Bool.TRUE);
			case FALSE:
				return mFactory.makeValue(Bool.FALSE);
			case UNKNOWN:
				return mFactory.makeValue(Bool.UNKNOWN);
			default:
				return mFactory.makeBottomValue();
			}
		case UNKNOWN:
			switch (bool) {
			case TRUE:
				return mFactory.makeValue(Bool.TRUE);
			case FALSE:
			case UNKNOWN:
				return mFactory.makeValue(Bool.UNKNOWN);
			default:
				return mFactory.makeBottomValue();
			}
		case EMPTY:
		default:
			return mFactory.makeBottomValue();
		}
	}

	/**
	 * @return A BoolValue representing the result of the operation: not value
	 */
	public BoolValue logicNot() {
		switch (mValue) {
		case TRUE:
			return mFactory.makeValue(Bool.FALSE);
		case FALSE:
			return mFactory.makeValue(Bool.TRUE);
		case UNKNOWN:
			return mFactory.makeValue(Bool.UNKNOWN);
		case EMPTY:
		default:
			return mFactory.makeBottomValue();
		}
	}

	@Override
	public BoolValue bitVectorConcat(IAbstractValue<?> value) {
		return null;
	}

	@Override
	public BoolValue bitVectorAccess(int start, int end) {
		return null;
	}

	/**
	 * Used to compare bool with not-bool, treating not-bool as false iff it is
	 * not-bool.bottom
	 * 
	 * @param value
	 * @return
	 */
	private BoolValue booleanFromAbstractValue(IAbstractValue<?> value) {
		if (value == null)
			return null;

		if (value instanceof BoolValue) {
			if (value.isBottom())
				return mFactory.makeBoolValue(false);
			return (BoolValue) value;
		}

		return mFactory.makeBoolValue(!value.isBottom());
	}

	@Override
	public String toString() {
		switch (mValue) {
		case TRUE:
			return "TRUE";
		case FALSE:
			return "FALSE";
		case UNKNOWN:
			return "UNKNOWN";
		case EMPTY:
		default:
			return "EMPTY";
		}
	}

	@Override
	public Term getTerm(Script script, Term variable) {
		Term value;
		if (getValue() == Bool.TRUE) {
			value = script.term("true");
		} else if (getValue() == Bool.FALSE) {
			value = script.term("false");
		} else {
			return script.term("true");
		}
		return script.term("=", variable, value);
	}
}
