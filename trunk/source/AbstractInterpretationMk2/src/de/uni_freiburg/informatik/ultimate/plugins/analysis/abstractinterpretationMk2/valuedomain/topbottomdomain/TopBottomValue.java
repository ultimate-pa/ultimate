/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.topbottomdomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IAbstractValueFactory;

/**
 * @author Christopher Dillo
 *
 */
public class TopBottomValue implements IAbstractValue<TopBottomValue.TopBottom> {

	public enum TopBottom {
		BOTTOM, TOP;
	}

	/**
	 * The actual value of this
	 */
	private TopBottom mValue;

	/**
	 * The factory for creating values like this
	 */
	private TopBottomValueFactory mFactory;

	/**
	 * The logger is needed in the operations
	 */
	private Logger mLogger;

	/**
	 * Constructor
	 * 
	 * @param value
	 * @param factory
	 * @param logger
	 */
	protected TopBottomValue(TopBottom value, TopBottomValueFactory factory, Logger logger) {
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
	public TopBottom getValue() {
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
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isFalse() {
		// TODO Auto-generated method stub
		return false;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.abstractdomain.IAbstractValue#isTop()
	 */
	@Override
	public boolean isTop() {
		return mValue == TopBottom.TOP;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.abstractdomain.IAbstractValue#isBottom()
	 */
	@Override
	public boolean isBottom() {
		return mValue == TopBottom.BOTTOM;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#representsSingleConcreteValue()
	 */
	@Override
	public boolean representsSingleConcreteValue() {
		return false;
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
		if (!(value instanceof TopBottomValue)) {
			return false;
		}
		TopBottomValue tbVal = (TopBottomValue) value;
		if (tbVal == null)
			return false;
		TopBottom tbvalue = tbVal.getValue();

		return mValue == tbvalue;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#isSuper(de.uni_freiburg .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain .IAbstractValue)
	 */
	@Override
	public boolean isSuperOrEqual(IAbstractValue<?> value) {
		return isTop() || isEqual(value);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#isSub(de.uni_freiburg .informatik.ultimate.plugins
	 * .analysis.abstractinterpretationMk2.abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean isSub(IAbstractValue<?> value) {
		if (value == null)
			return false;

		return value.isTop() || isEqual(value);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.abstractdomain.IAbstractValue#copy()
	 */
	@Override
	public TopBottomValue copy() {
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
	public TopBottomValue add(IAbstractValue<?> value) {
		return mFactory.makeTopValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#subtract(de.uni_freiburg .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain .IAbstractValue)
	 */
	@Override
	public TopBottomValue subtract(IAbstractValue<?> value) {
		return mFactory.makeTopValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#multiply(de.uni_freiburg .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain .IAbstractValue)
	 */
	@Override
	public TopBottomValue multiply(IAbstractValue<?> value) {
		return mFactory.makeTopValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#divide(de.uni_freiburg .informatik.ultimate.
	 * plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue divide(IAbstractValue<?> value) {
		return mFactory.makeTopValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#modulo(de.uni_freiburg .informatik.ultimate.
	 * plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue modulo(IAbstractValue<?> value) {
		return mFactory.makeTopValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.abstractdomain.IAbstractValue#negative()
	 */
	@Override
	public TopBottomValue negative() {
		return mFactory.makeTopValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#compareIsEqual(de. uni_freiburg.informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2 .abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue compareIsEqual(IAbstractValue<?> value) {
		return isEqual(value) ? copy() : mFactory.makeBottomValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#compareIsNotEqual( de.uni_freiburg.informatik
	 * .ultimate.plugins.analysis.abstractinterpretationMk2 .abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue compareIsNotEqual(IAbstractValue<?> value) {
		return copy();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#compareIsLess(de.uni_freiburg .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain .IAbstractValue)
	 */
	@Override
	public TopBottomValue compareIsLess(IAbstractValue<?> value) {
		return isEqual(value) ? copy() : mFactory.makeBottomValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#compareIsGreater(de .uni_freiburg.informatik
	 * .ultimate.plugins.analysis.abstractinterpretationMk2 .abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue compareIsGreater(IAbstractValue<?> value) {
		return isEqual(value) ? copy() : mFactory.makeBottomValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#compareIsLessEqual (de.uni_freiburg.informatik
	 * .ultimate.plugins.analysis.abstractinterpretationMk2 .abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue compareIsLessEqual(IAbstractValue<?> value) {
		return isEqual(value) ? copy() : mFactory.makeBottomValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#compareIsGreaterEqual (de.uni_freiburg.informatik
	 * .ultimate.plugins.analysis.abstractinterpretationMk2 .abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue compareIsGreaterEqual(IAbstractValue<?> value) {
		return isEqual(value) ? copy() : mFactory.makeBottomValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#logicIff(de.uni_freiburg .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain .IAbstractValue)
	 */
	@Override
	public TopBottomValue logicIff(IAbstractValue<?> value) {
		return mFactory.makeTopValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#logicImplies(de.uni_freiburg .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain .IAbstractValue)
	 */
	@Override
	public TopBottomValue logicImplies(IAbstractValue<?> value) {
		return mFactory.makeTopValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#logicAnd(de.uni_freiburg .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain .IAbstractValue)
	 */
	@Override
	public TopBottomValue logicAnd(IAbstractValue<?> value) {
		return mFactory.makeTopValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#logicOr(de.uni_freiburg .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain .IAbstractValue)
	 */
	@Override
	public TopBottomValue logicOr(IAbstractValue<?> value) {
		return mFactory.makeTopValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.abstractdomain.IAbstractValue#logicNot()
	 */
	@Override
	public TopBottomValue logicNot() {
		return mFactory.makeTopValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#bitVectorConcat(de .uni_freiburg.informatik.
	 * ultimate.plugins.analysis.abstractinterpretationMk2 .abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue bitVectorConcat(IAbstractValue<?> value) {
		return mFactory.makeTopValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue#bitVectorAccess(int, int)
	 */
	@Override
	public TopBottomValue bitVectorAccess(int start, int end) {
		return mFactory.makeTopValue();
	}

	public String toString() {
		switch (mValue) {
		case BOTTOM:
			return "BOTTOM";
		case TOP:
			return "TOP";
		default:
			return "ERROR";
		}
	}

	@Override
	public Term getTerm(Script script, Term variable) {
		switch (mValue) {
		case BOTTOM:
			return script.term("false");
		case TOP:
			return script.term("true");
		default:
			throw new UnsupportedOperationException("Unknown value " + mValue);
		}
	}
}
