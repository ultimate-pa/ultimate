/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.paritydomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
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
	 * Generate a new ParityValue with the given value
	 * 
	 * @param value
	 *            ZERO? PLUSMINUS?
	 */
	protected ParityValue(Parity value, ParityValueFactory factory, Logger logger) {
		mValue = value;
		mFactory = factory;
	}

	@Override
	public Parity getValue() {
		return mValue;
	}

	@Override
	public IAbstractValueFactory<?> getFactory() {
		return mFactory;
	}

	@Override
	public boolean isTrue() {
		return false;
	}

	@Override
	public boolean isFalse() {
		// TODO Auto-generated method stub
		return mValue == Parity.ODD;
	}

	@Override
	public boolean isTop() {
		return (mValue == Parity.TOP);
	}

	@Override
	public boolean isBottom() {
		return (mValue == Parity.EMPTY);
	}

	@Override
	public boolean representsSingleConcreteValue() {
		return false;
	}

	@Override
	public boolean isEqual(IAbstractValue<?> value) {
		ParityValue parityVal = (ParityValue) value;
		return (mValue == parityVal.getValue());
	}

	@Override
	public boolean isSuperOrEqual(IAbstractValue<?> value) {
		ParityValue parityVal = (ParityValue) value;
		if (parityVal == null)
			return false;

		return mValue == Parity.TOP || mValue == parityVal.getValue() || parityVal.getValue() == Parity.EMPTY;
	}

	@Override
	public boolean isSub(IAbstractValue<?> value) {
		ParityValue parityVal = (ParityValue) value;
		if (parityVal == null)
			return false;

		return mValue == Parity.EMPTY || mValue == parityVal.getValue() || parityVal.getValue() == Parity.TOP;
	}

	@Override
	public ParityValue copy() {
		return mFactory.makeValue(mValue);
	}

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

	@Override
	public ParityValue subtract(IAbstractValue<?> value) {
		return add(value);
	}

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

	@Override
	public ParityValue negative() {
		return this;
	}

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

	@Override
	public ParityValue compareIsLess(IAbstractValue<?> value) {
		return compareIsNotEqual(value);
	}

	@Override
	public ParityValue compareIsGreater(IAbstractValue<?> value) {
		return compareIsNotEqual(value);
	}

	@Override
	public ParityValue compareIsLessEqual(IAbstractValue<?> value) {
		return compareIsNotEqual(value);
	}

	@Override
	public ParityValue compareIsGreaterEqual(IAbstractValue<?> value) {
		return compareIsLessEqual(value);
	}

	@Override
	public ParityValue logicIff(IAbstractValue<?> value) {
		return null;
	}

	@Override
	public ParityValue logicImplies(IAbstractValue<?> value) {
		return null;
	}

	@Override
	public ParityValue logicAnd(IAbstractValue<?> value) {
		return null;
	}

	@Override
	public ParityValue logicOr(IAbstractValue<?> value) {
		return null;
	}

	@Override
	public ParityValue logicNot() {
		return null;
	}

	@Override
	public ParityValue bitVectorConcat(IAbstractValue<?> value) {
		return null;
	}

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

	@Override
	public Term getTerm(Script script, Term variable) {
		switch (mValue) {
		case EMPTY:
			return script.term("false");
		case EVEN:
			return script.term("=", script.term("mod", variable, script.numeral("2"), script.numeral("0")));
		case ODD:
			return script.term("=", script.term("mod", variable, script.numeral("2"), script.numeral("1")));
		case TOP:
			return script.term("true");
		default:
			throw new UnsupportedOperationException("Unknown parity value: " + mValue);
		}
	}
}
