/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.paritydomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IAbstractValueFactory;

/**
 * @author Jan Hättig
 *
 */
public class ParityValue implements IAbstractValue<ParityValue.Parity> {

	/**
	 * parity for positive values assume that -1 has parity odd and -2 is even
	 */
	public enum Parity {
		EMPTY, ODD, EVEN, TOP
	}

	/**
	 * The actual value of this
	 */
	private Parity mValue;

	/**
	 * The factory for creating values like this
	 */
	private ParityValueFactory mFactory;

	/**
	 * The logger is needed in the operations
	 */
	private Logger mLogger;

	/**
	 * Generate a new ParityValue with the given value
	 * 
	 * @param value
	 *            ZERO? PLUSMINUS?
	 */
	protected ParityValue(Parity value, ParityValueFactory factory,
			Logger logger) {
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
	public Parity getValue() {
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

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.valuedomain.IAbstractValue#isTrue()
	 */
	@Override
	public boolean isTrue() {
		return false;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.valuedomain.IAbstractValue#isFalse()
	 */
	@Override
	public boolean isFalse() {
		// TODO Auto-generated method stub
		return mValue == Parity.ODD;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.abstractdomain.IAbstractValue#isTop()
	 */
	@Override
	public boolean isTop() {
		return (mValue == Parity.TOP);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.abstractdomain.IAbstractValue#isBottom()
	 */
	@Override
	public boolean isBottom() {
		return (mValue == Parity.EMPTY);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#representsSingleConcreteValue()
	 */
	@Override
	public boolean representsSingleConcreteValue() {
		return false;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#isEqual(de.uni_freiburg
	 * .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain
	 * .IAbstractValue)
	 */
	@Override
	public boolean isEqual(IAbstractValue<?> value) {
		ParityValue parityVal = (ParityValue) value;
		return (mValue == parityVal.getValue());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#isGreater(de.uni_freiburg
	 * .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain
	 * .IAbstractValue)
	 */
	@Override
	public boolean isSuperOrEqual(IAbstractValue<?> value) {
		ParityValue parityVal = (ParityValue) value;
		if (parityVal == null)
			return false;

		return mValue == Parity.TOP || mValue == parityVal.getValue()
				|| parityVal.getValue() == Parity.EMPTY;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#isLesser(de.uni_freiburg
	 * .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain
	 * .IAbstractValue)
	 */
	@Override
	public boolean isSub(IAbstractValue<?> value) {
		ParityValue parityVal = (ParityValue) value;
		if (parityVal == null)
			return false;

		return mValue == Parity.EMPTY || mValue == parityVal.getValue()
				|| parityVal.getValue() == Parity.TOP;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.abstractdomain.IAbstractValue#copy()
	 */
	@Override
	public ParityValue copy() {
		return mFactory.makeValue(mValue);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#add(de.uni_freiburg
	 * .informatik.ultimate.plugins
	 * .analysis.abstractinterpretationMk2.abstractdomain.IAbstractValue)
	 */
	@Override
	public ParityValue add(IAbstractValue<?> value) {
		ParityValue parityVal = (ParityValue) value;
		if (parityVal == null) {
			return mFactory.makeBottomValue();
		}
		Parity otherParity = parityVal.getValue();

		switch (mValue) {
		case EVEN:
			switch (otherParity) {
			case EVEN:
				return this;
			case ODD:
				return parityVal;

			}
		case ODD:
			switch (otherParity) {
			case EVEN:
				return this;
			case ODD:
				return mFactory.makeValue(Parity.EVEN);
			default:
				return mFactory.makeBottomValue();
			}
		}
		return mFactory.makeBottomValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#subtract(de.uni_freiburg
	 * .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain
	 * .IAbstractValue)
	 */
	@Override
	public ParityValue subtract(IAbstractValue<?> value) {
		return add(value);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#multiply(de.uni_freiburg
	 * .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain
	 * .IAbstractValue)
	 */
	@Override
	public ParityValue multiply(IAbstractValue<?> value) {
		ParityValue parityVal = (ParityValue) value;
		if (parityVal == null) {
			return mFactory.makeBottomValue();
		}
		Parity otherParity = parityVal.getValue();

		if (otherParity == Parity.EMPTY || mValue == Parity.EMPTY) {
			return parityVal;
		}
		if (otherParity == Parity.EVEN || mValue == Parity.EVEN) {
			return mFactory.makeValue(Parity.EVEN);
		}
		if (otherParity == Parity.ODD && mValue == Parity.ODD) {
			return mFactory.makeValue(Parity.ODD);
		}
		return mFactory.makeValue(Parity.TOP);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#divide(de.uni_freiburg
	 * .informatik.ultimate.
	 * plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractValue)
	 */
	@Override
	public ParityValue divide(IAbstractValue<?> value) {
		ParityValue parityVal = (ParityValue) value;
		if (value == null)
			return mFactory.makeBottomValue();
		Parity otherParity = parityVal.getValue();

		if (otherParity == Parity.EMPTY || otherParity == Parity.EMPTY) {
			return mFactory.makeValue(Parity.EMPTY);
		}

		return mFactory.makeTopValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#modulo(de.uni_freiburg
	 * .informatik.ultimate.
	 * plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractValue)
	 */
	@Override
	public ParityValue modulo(IAbstractValue<?> value) {
		ParityValue parityVal = (ParityValue) value;
		if (parityVal == null) {
			return mFactory.makeBottomValue();
		}
		Parity otherParity = parityVal.getValue();

		if (otherParity == Parity.EMPTY || otherParity == Parity.EMPTY) {
			return mFactory.makeValue(Parity.EMPTY);
		}

		// when dividing by something even, a same parity
		// rest remains
		if (otherParity == Parity.EVEN) {
			return this;
		}

		return mFactory.makeTopValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.abstractdomain.IAbstractValue#negation()
	 */
	@Override
	public ParityValue negative() {
		return this;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#compareIsEqual(de.
	 * uni_freiburg.informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue)
	 */
	@Override
	public ParityValue compareIsEqual(IAbstractValue<?> value) {
		ParityValue ParityVal = (ParityValue) value;
		if (ParityVal == null)
			return mFactory.makeBottomValue();
		Parity otherParity = ParityVal.getValue();

		if (mValue == otherParity)
			return mFactory.makeValue(mValue);

		switch (mValue) {
		case EVEN:
			switch (otherParity) {
			case EVEN:
			case TOP:
				return this;
			}
		case ODD:
			switch (otherParity) {
			case ODD:
			case TOP:
				return this;
			}
		case TOP:
			return ParityVal;
		}
		return mFactory.makeBottomValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#compareIsNotEqual(
	 * de.uni_freiburg.informatik
	 * .ultimate.plugins.analysis.abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue)
	 */
	@Override
	public ParityValue compareIsNotEqual(IAbstractValue<?> value) {
		ParityValue ParityVal = (ParityValue) value;
		if (ParityVal == null)
			return mFactory.makeBottomValue();
		Parity otherParity = ParityVal.getValue();

		if (mValue == otherParity)
			return mFactory.makeValue(mValue);

		switch (mValue) {
		case EVEN:
			switch (otherParity) {
			case EVEN:
				return ParityVal;
			case TOP:
			case ODD:
				return mFactory.makeValue(Parity.TOP);
			}
		case ODD:
			switch (otherParity) {
			case ODD:
				return ParityVal;
			case EVEN:
			case TOP:
				return mFactory.makeValue(Parity.TOP);
			}
		case TOP:
			if (otherParity == Parity.EMPTY) {
				return ParityVal;
			}
			return this;
		}
		return mFactory.makeBottomValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#compareIsLess(de.uni_freiburg
	 * .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain
	 * .IAbstractValue)
	 */
	@Override
	public ParityValue compareIsLess(IAbstractValue<?> value) {
		return compareIsNotEqual(value);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#compareIsGreater(de
	 * .uni_freiburg.informatik
	 * .ultimate.plugins.analysis.abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue)
	 */
	@Override
	public ParityValue compareIsGreater(IAbstractValue<?> value) {
		return compareIsNotEqual(value);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#compareIsLessEqual
	 * (de.uni_freiburg.informatik
	 * .ultimate.plugins.analysis.abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue)
	 */
	@Override
	public ParityValue compareIsLessEqual(IAbstractValue<?> value) {
		return compareIsNotEqual(value);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#compareIsGreaterEqual
	 * (de.uni_freiburg.informatik
	 * .ultimate.plugins.analysis.abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue)
	 */
	@Override
	public ParityValue compareIsGreaterEqual(IAbstractValue<?> value) {
		return compareIsLessEqual(value);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#logicIff(de.uni_freiburg
	 * .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain
	 * .IAbstractValue)
	 */
	@Override
	public ParityValue logicIff(IAbstractValue<?> value) {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#logicImplies(de.uni_freiburg
	 * .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain
	 * .IAbstractValue)
	 */
	@Override
	public ParityValue logicImplies(IAbstractValue<?> value) {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#logicAnd(de.uni_freiburg
	 * .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain
	 * .IAbstractValue)
	 */
	@Override
	public ParityValue logicAnd(IAbstractValue<?> value) {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#logicOr(de.uni_freiburg
	 * .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain
	 * .IAbstractValue)
	 */
	@Override
	public ParityValue logicOr(IAbstractValue<?> value) {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.abstractdomain.IAbstractValue#logicNot()
	 */
	@Override
	public ParityValue logicNot() {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#bitVectorConcat(de
	 * .uni_freiburg.informatik.
	 * ultimate.plugins.analysis.abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue)
	 */
	@Override
	public ParityValue bitVectorConcat(IAbstractValue<?> value) {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#bitVectorAccess(int, int)
	 */
	@Override
	public ParityValue bitVectorAccess(int start, int end) {
		return null;
	}

	@Override
	public String toString() {
		switch (mValue) {
		case EVEN:
			return "Parity: Even";
		case ODD:
			return "Parity: Odd";
		case TOP:
			return "Parity: unknown";
		default:
			return "Parity: empty";
		}
	}
}
