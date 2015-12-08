/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.signdomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IAbstractValueFactory;

/**
 * @author Christopher Dillo
 *
 */
public class SignValue implements IAbstractValue<SignValue.Sign> {

	/**
	 * Possible values for the sign domain. EMPTY < ZERO, PLUS, MINUS < PLUSMINUS ZERO, PLUS, MINUS : no relation ZERO :
	 * 0 PLUS : > 0 MINUS : < 0
	 */
	public enum Sign {
		EMPTY, // Bottom
		ZERO, PLUS, MINUS, PLUSMINUS // Top
	}

	/**
	 * The actual value of this
	 */
	private Sign mValue;

	/**
	 * The factory for creating values like this
	 */
	private SignValueFactory mFactory;

	/**
	 * The logger is needed in the operations
	 */
	private Logger mLogger;

	/**
	 * Generate a new SignValue with the given value
	 * 
	 * @param value
	 *            ZERO? PLUSMINUS?
	 */
	protected SignValue(Sign value, SignValueFactory factory, Logger logger) {
		mValue = value;
		mFactory = factory;
		mLogger = logger;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.abstractdomain.IAbstractValue#getValue()
	 */
	@Override
	public Sign getValue() {
		return mValue;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.valuedomain.IAbstractValue#getFactory()
	 */
	@Override
	public IAbstractValueFactory<?> getFactory() {
		return mFactory;
	}

	@Override
	public boolean isTrue() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isFalse() {
		// TODO Auto-generated method stub
		return mValue == Sign.MINUS || mValue == Sign.ZERO;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.abstractdomain.IAbstractValue#isTop()
	 */
	@Override
	public boolean isTop() {
		return (mValue == Sign.PLUSMINUS);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.abstractdomain.IAbstractValue#isBottom()
	 */
	@Override
	public boolean isBottom() {
		return (mValue == Sign.EMPTY);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#representsSingleConcreteValue()
	 */
	@Override
	public boolean representsSingleConcreteValue() {
		return (mValue == Sign.PLUS) || (mValue == Sign.MINUS) || (mValue == Sign.ZERO);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#isEqual(de.uni_freiburg .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain .IAbstractValue)
	 */
	@Override
	public boolean isEqual(IAbstractValue<?> value) {
		SignValue signVal = (SignValue) value;
		if (signVal == null)
			return false;

		return (mValue == signVal.getValue());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#isGreater(de.uni_freiburg .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain .IAbstractValue)
	 */
	@Override
	public boolean isSuperOrEqual(IAbstractValue<?> value) {
		SignValue signVal = (SignValue) value;
		if (signVal == null)
			return false;

		if (mValue == Sign.PLUSMINUS)
			return true;

		if (mValue == signVal.getValue())
			return true;

		if (signVal.getValue() == Sign.EMPTY)
			return true;

		return false;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#isLesser(de.uni_freiburg .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain .IAbstractValue)
	 */
	@Override
	public boolean isSub(IAbstractValue<?> value) {
		SignValue signVal = (SignValue) value;
		if (signVal == null)
			return false;

		if (mValue == Sign.EMPTY)
			return true;

		if (mValue == signVal.getValue())
			return true;

		if (signVal.getValue() == Sign.PLUSMINUS)
			return true;

		return false;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.abstractdomain.IAbstractValue#copy()
	 */
	@Override
	public SignValue copy() {
		return mFactory.makeValue(mValue);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#add(de.uni_freiburg .informatik.ultimate.plugins
	 * .analysis.abstractinterpretationMk2.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue add(IAbstractValue<?> value) {
		SignValue signVal = (SignValue) value;
		if (signVal == null)
			return mFactory.makeBottomValue();
		Sign otherSign = signVal.getValue();

		switch (mValue) {
		case ZERO:
			return mFactory.makeValue(otherSign);
		case PLUS:
			switch (otherSign) {
			case ZERO:
			case PLUS:
				return mFactory.makeValue(Sign.PLUS);
			case MINUS:
			case PLUSMINUS:
				return mFactory.makeValue(Sign.PLUSMINUS);
			default:
				return mFactory.makeBottomValue();
			}
		case MINUS:
			switch (otherSign) {
			case ZERO:
			case MINUS:
				return mFactory.makeValue(Sign.MINUS);
			case PLUS:
			case PLUSMINUS:
				return mFactory.makeValue(Sign.PLUSMINUS);
			default:
				return mFactory.makeBottomValue();
			}
		case PLUSMINUS:
			return mFactory.makeValue(Sign.PLUSMINUS);
		default:
			return mFactory.makeBottomValue();
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#subtract(de.uni_freiburg .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain .IAbstractValue)
	 */
	@Override
	public SignValue subtract(IAbstractValue<?> value) {
		SignValue signVal = (SignValue) value;
		if (signVal == null)
			return mFactory.makeBottomValue();
		Sign otherSign = signVal.getValue();

		switch (mValue) {
		case ZERO:
			switch (otherSign) {
			case ZERO:
			case PLUSMINUS:
				return mFactory.makeValue(otherSign);
			case PLUS:
				return mFactory.makeValue(Sign.MINUS);
			case MINUS:
				return mFactory.makeValue(Sign.PLUS);
			default:
				return mFactory.makeBottomValue();
			}
		case PLUS:
			switch (otherSign) {
			case ZERO:
			case MINUS:
				return mFactory.makeValue(Sign.PLUS);
			case PLUS:
			case PLUSMINUS:
				return mFactory.makeValue(Sign.PLUSMINUS);
			default:
				return mFactory.makeBottomValue();
			}
		case MINUS:
			switch (otherSign) {
			case ZERO:
			case PLUS:
				return mFactory.makeValue(Sign.MINUS);
			case MINUS:
			case PLUSMINUS:
				return mFactory.makeValue(Sign.PLUSMINUS);
			default:
				return mFactory.makeBottomValue();
			}
		case PLUSMINUS:
			return mFactory.makeValue(Sign.PLUSMINUS);
		default:
			return mFactory.makeBottomValue();
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#multiply(de.uni_freiburg .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain .IAbstractValue)
	 */
	@Override
	public SignValue multiply(IAbstractValue<?> value) {
		SignValue signVal = (SignValue) value;
		if (signVal == null)
			return mFactory.makeBottomValue();
		Sign otherSign = signVal.getValue();

		switch (mValue) {
		case ZERO:
			return mFactory.makeValue(Sign.ZERO);
		case PLUS:
			switch (otherSign) {
			case ZERO:
				return mFactory.makeValue(Sign.ZERO);
			case PLUS:
				return mFactory.makeValue(Sign.PLUS);
			case MINUS:
				return mFactory.makeValue(Sign.MINUS);
			case PLUSMINUS:
				return mFactory.makeValue(Sign.PLUSMINUS);
			default:
				return mFactory.makeBottomValue();
			}
		case MINUS:
			switch (otherSign) {
			case ZERO:
				return mFactory.makeValue(Sign.ZERO);
			case PLUS:
				return mFactory.makeValue(Sign.MINUS);
			case MINUS:
				return mFactory.makeValue(Sign.PLUS);
			case PLUSMINUS:
				return mFactory.makeValue(Sign.PLUSMINUS);
			default:
				return mFactory.makeBottomValue();
			}
		case PLUSMINUS:
			return mFactory.makeValue(Sign.PLUSMINUS);
		default:
			return mFactory.makeBottomValue();
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#divide(de.uni_freiburg .informatik.ultimate.
	 * plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue divide(IAbstractValue<?> value) {
		if (value == null)
			return mFactory.makeBottomValue();

		if ((value.getValue() == Sign.ZERO) || (value.getValue() == Sign.PLUSMINUS)) {
			mLogger.warn(String.format("Potential division by zero: %s / %s", this, value));
			return mFactory.makeBottomValue();
		}

		return this.multiply(value);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#modulo(de.uni_freiburg .informatik.ultimate.
	 * plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue modulo(IAbstractValue<?> value) {
		if (value == null)
			return mFactory.makeBottomValue();

		if ((value.getValue() == Sign.ZERO) || (value.getValue() == Sign.PLUSMINUS)) {
			mLogger.warn(String.format("Potential modulo division by zero: %s %% %s", this, value));
			return mFactory.makeBottomValue();
		}

		return mFactory.makeValue(Sign.PLUSMINUS); // remainder is always >= 0,
													// which is only covered by
													// PLUSMINUS
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.abstractdomain.IAbstractValue#negation()
	 */
	@Override
	public SignValue negative() {
		switch (mValue) {
		case PLUS:
			return mFactory.makeValue(Sign.MINUS);
		case MINUS:
			return mFactory.makeValue(Sign.PLUS);
		default:
			return mFactory.makeValue(mValue);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#compareIsEqual(de. uni_freiburg.informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2 .abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue compareIsEqual(IAbstractValue<?> value) {
		SignValue signVal = (SignValue) value;
		if (signVal == null)
			return mFactory.makeBottomValue();
		Sign otherSign = signVal.getValue();

		if (mValue == otherSign)
			return mFactory.makeValue(mValue);

		switch (mValue) {
		case ZERO:
			switch (otherSign) {
			case ZERO:
			case PLUSMINUS:
				return mFactory.makeValue(Sign.ZERO);
			case MINUS:
			case PLUS:
			default:
				return mFactory.makeBottomValue();
			}
		case PLUS:
			switch (otherSign) {
			case PLUS:
			case PLUSMINUS:
				return mFactory.makeValue(Sign.PLUS);
			case ZERO:
			case MINUS:
			default:
				return mFactory.makeBottomValue();
			}
		case MINUS:
			switch (otherSign) {
			case MINUS:
			case PLUSMINUS:
				return mFactory.makeValue(Sign.MINUS);
			case ZERO:
			case PLUS:
			default:
				return mFactory.makeBottomValue();
			}
		case PLUSMINUS:
			return mFactory.makeValue(otherSign);
		default:
			return mFactory.makeBottomValue();
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#compareIsNotEqual( de.uni_freiburg.informatik
	 * .ultimate.plugins.analysis.abstractinterpretationMk2 .abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue compareIsNotEqual(IAbstractValue<?> value) {
		SignValue signVal = (SignValue) value;
		if (signVal == null)
			return mFactory.makeBottomValue();
		Sign otherSign = signVal.getValue();

		switch (mValue) {
		case ZERO:
			switch (otherSign) {
			case ZERO:
				return mFactory.makeBottomValue();
			default:
				return mFactory.makeValue(otherSign);
			}
		case PLUS:
			switch (otherSign) {
			case PLUS:
				return mFactory.makeValue(Sign.PLUS);
			case ZERO:
			case MINUS:
			case PLUSMINUS:
				return mFactory.makeValue(Sign.PLUSMINUS);
			default:
				return mFactory.makeBottomValue();
			}
		case MINUS:
			switch (otherSign) {
			case MINUS:
				return mFactory.makeValue(Sign.MINUS);
			case PLUS:
			case ZERO:
			case PLUSMINUS:
				return mFactory.makeValue(Sign.PLUSMINUS);
			default:
				return mFactory.makeBottomValue();
			}
		case PLUSMINUS:
			return mFactory.makeValue(Sign.PLUSMINUS);
		default:
			return mFactory.makeBottomValue();
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#compareIsLess(de.uni_freiburg .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain .IAbstractValue)
	 */
	@Override
	public SignValue compareIsLess(IAbstractValue<?> value) {
		SignValue signVal = (SignValue) value;
		if (signVal == null)
			return mFactory.makeBottomValue();
		Sign otherSign = signVal.getValue();

		switch (mValue) {
		case ZERO:
			switch (otherSign) {
			case PLUS:
			case PLUSMINUS:
				return mFactory.makeValue(Sign.ZERO);
			case ZERO:
			case MINUS:
			default:
				return mFactory.makeBottomValue();
			}
		case PLUS:
			switch (otherSign) {
			case PLUS:
			case PLUSMINUS:
				return mFactory.makeValue(Sign.PLUS);
			case ZERO:
			case MINUS:
			default:
				return mFactory.makeBottomValue();
			}
		case MINUS:
			return mFactory.makeValue((otherSign == Sign.EMPTY) ? Sign.EMPTY : Sign.MINUS);
		case PLUSMINUS:
			switch (otherSign) {
			case ZERO:
			case MINUS:
				return mFactory.makeValue(Sign.MINUS);
			case PLUS:
			case PLUSMINUS:
				return mFactory.makeValue(Sign.PLUSMINUS);
			default:
				return mFactory.makeBottomValue();
			}
		default:
			return mFactory.makeBottomValue();
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#compareIsGreater(de .uni_freiburg.informatik
	 * .ultimate.plugins.analysis.abstractinterpretationMk2 .abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue compareIsGreater(IAbstractValue<?> value) {
		SignValue signVal = (SignValue) value;
		if (signVal == null)
			return mFactory.makeBottomValue();
		Sign otherSign = signVal.getValue();

		switch (mValue) {
		case ZERO:
			switch (otherSign) {
			case MINUS:
			case PLUSMINUS:
				return mFactory.makeValue(Sign.ZERO);
			case ZERO:
			case PLUS:
			default:
				return mFactory.makeBottomValue();
			}
		case PLUS:
			return mFactory.makeValue((otherSign == Sign.EMPTY) ? Sign.EMPTY : Sign.PLUS);
		case MINUS:
			switch (otherSign) {
			case MINUS:
			case PLUSMINUS:
				return mFactory.makeValue(Sign.MINUS);
			case ZERO:
			case PLUS:
			default:
				return mFactory.makeBottomValue();
			}
		case PLUSMINUS:
			switch (otherSign) {
			case ZERO:
			case PLUS:
				return mFactory.makeValue(Sign.PLUS);
			case MINUS:
			case PLUSMINUS:
				return mFactory.makeValue(Sign.PLUSMINUS);
			default:
				return mFactory.makeBottomValue();
			}
		default:
			return mFactory.makeBottomValue();
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#compareIsLessEqual (de.uni_freiburg.informatik
	 * .ultimate.plugins.analysis.abstractinterpretationMk2 .abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue compareIsLessEqual(IAbstractValue<?> value) {
		SignValue signVal = (SignValue) value;
		if (signVal == null)
			return mFactory.makeBottomValue();
		Sign otherSign = signVal.getValue();

		switch (mValue) {
		case ZERO:
			switch (otherSign) {
			case ZERO:
			case PLUS:
			case PLUSMINUS:
				return mFactory.makeValue(Sign.ZERO);
			case MINUS:
			default:
				return mFactory.makeBottomValue();
			}
		case PLUS:
			switch (otherSign) {
			case PLUS:
			case PLUSMINUS:
				return mFactory.makeValue(Sign.PLUS);
			case ZERO:
			case MINUS:
			default:
				return mFactory.makeBottomValue();
			}
		case MINUS:
			return mFactory.makeValue((otherSign == Sign.EMPTY) ? Sign.EMPTY : Sign.MINUS);
		case PLUSMINUS:
			switch (otherSign) {
			case ZERO:
			case MINUS:
				return mFactory.makeValue(Sign.MINUS);
			case PLUS:
			case PLUSMINUS:
				return mFactory.makeValue(Sign.PLUSMINUS);
			default:
				return mFactory.makeBottomValue();
			}
		default:
			return mFactory.makeBottomValue();
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#compareIsGreaterEqual (de.uni_freiburg.informatik
	 * .ultimate.plugins.analysis.abstractinterpretationMk2 .abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue compareIsGreaterEqual(IAbstractValue<?> value) {
		SignValue signVal = (SignValue) value;
		if (signVal == null)
			return mFactory.makeBottomValue();
		Sign otherSign = signVal.getValue();

		switch (mValue) {
		case ZERO:
			switch (otherSign) {
			case ZERO:
			case MINUS:
			case PLUSMINUS:
				return mFactory.makeValue(Sign.ZERO);
			case PLUS:
			default:
				return mFactory.makeBottomValue();
			}
		case PLUS:
			return mFactory.makeValue((otherSign == Sign.EMPTY) ? Sign.EMPTY : Sign.PLUS);
		case MINUS:
			switch (otherSign) {
			case MINUS:
			case PLUSMINUS:
				return mFactory.makeValue(Sign.MINUS);
			case ZERO:
			case PLUS:
			default:
				return mFactory.makeBottomValue();
			}
		case PLUSMINUS:
			switch (otherSign) {
			case ZERO:
			case PLUS:
				return mFactory.makeValue(Sign.PLUS);
			case MINUS:
			case PLUSMINUS:
				return mFactory.makeValue(Sign.PLUSMINUS);
			default:
				return mFactory.makeBottomValue();
			}
		default:
			return mFactory.makeBottomValue();
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#logicIff(de.uni_freiburg .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain .IAbstractValue)
	 */
	@Override
	public SignValue logicIff(IAbstractValue<?> value) {
		return mFactory.makeBottomValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#logicImplies(de.uni_freiburg .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain .IAbstractValue)
	 */
	@Override
	public SignValue logicImplies(IAbstractValue<?> value) {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#logicAnd(de.uni_freiburg .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain .IAbstractValue)
	 */
	@Override
	public SignValue logicAnd(IAbstractValue<?> value) {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#logicOr(de.uni_freiburg .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain .IAbstractValue)
	 */
	@Override
	public SignValue logicOr(IAbstractValue<?> value) {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.abstractdomain.IAbstractValue#logicNot()
	 */
	@Override
	public SignValue logicNot() {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#bitVectorConcat(de .uni_freiburg.informatik.
	 * ultimate.plugins.analysis.abstractinterpretationMk2 .abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue bitVectorConcat(IAbstractValue<?> value) {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#bitVectorAccess(int, int)
	 */
	@Override
	public SignValue bitVectorAccess(int start, int end) {
		return null;
	}

	@Override
	public String toString() {
		switch (mValue) {
		case ZERO:
			return "Sign: 0";
		case PLUS:
			return "Sign: +";
		case MINUS:
			return "Sign: -";
		case PLUSMINUS:
			return "Sign: +-";
		default:
			return "Sign: empty";
		}
	}

	@Override
	public Term getTerm(Script script, Term variable) {
		switch (getValue()) {
		case EMPTY:
			return script.term("false");
		case MINUS:
			return script.term(">", script.numeral("0"), variable);
		case PLUS:
			return script.term("<", script.numeral("0"), variable);
		case PLUSMINUS:
			return script.term("true");
		case ZERO:
			return script.term("=", script.numeral("0"), variable);
		default:
			throw new UnsupportedOperationException("Forgot a case");
		}
	}
}
