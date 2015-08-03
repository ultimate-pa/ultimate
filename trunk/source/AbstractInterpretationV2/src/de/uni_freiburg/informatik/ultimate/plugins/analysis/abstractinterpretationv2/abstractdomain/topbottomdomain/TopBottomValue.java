/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.topbottomdomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.valuedomain.IAbstractValue;

/**
 * @author Christopher Dillo
 *
 */
public class TopBottomValue implements IAbstractValue<TopBottomValue.TopBottom> {
	
	public enum TopBottom {
		BOTTOM, TOP;
	}
	
	private TopBottom m_value;
	
	private TopBottomValueFactory m_factory;
	
	private Logger m_logger;
	
	protected TopBottomValue(TopBottom value, TopBottomValueFactory factory, Logger logger) {
		m_value = value;
		m_factory = factory;
		m_logger = logger;
		m_logger.warn("TOP-BOTTOM domain offers very imprecise analysis only.");
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#getValue()
	 */
	@Override
	public TopBottom getValue() {
		return m_value;
	}

	@Override
	public boolean isTrue()
	{
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isFalse()
	{
		// TODO Auto-generated method stub
		return false;
	}
	
	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#isTop()
	 */
	@Override
	public boolean isTop() {
		return m_value == TopBottom.TOP;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#isBottom()
	 */
	@Override
	public boolean isBottom() {
		return m_value == TopBottom.BOTTOM;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#representsSingleConcreteValue()
	 */
	@Override
	public boolean representsSingleConcreteValue() {
		return false;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#isEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean isEqual(IAbstractValue<?> value) {
		TopBottomValue tbVal = (TopBottomValue) value;
		if (tbVal == null) return false;
		TopBottom tbvalue = tbVal.getValue();
		
		return m_value == tbvalue;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#isSuper(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean isSuper(IAbstractValue<?> value) {
		return isTop() || isEqual(value);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#isSub(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean isSub(IAbstractValue<?> value) {
		if (value == null)
			return false;

		return value.isTop() || isEqual(value);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#copy()
	 */
	@Override
	public TopBottomValue copy() {
		return m_factory.makeValue(m_value);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#add(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue add(IAbstractValue<?> value) {
		return m_factory.makeTopValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#subtract(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue subtract(IAbstractValue<?> value) {
		return m_factory.makeTopValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#multiply(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue multiply(IAbstractValue<?> value) {
		return m_factory.makeTopValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#divide(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue divide(IAbstractValue<?> value) {
		return m_factory.makeTopValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#modulo(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue modulo(IAbstractValue<?> value) {
		return m_factory.makeTopValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#negative()
	 */
	@Override
	public TopBottomValue negative() {
		return m_factory.makeTopValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#compareIsEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue compareIsEqual(IAbstractValue<?> value) {
		return isEqual(value) ? copy() : m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#compareIsNotEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue compareIsNotEqual(IAbstractValue<?> value) {
		return copy();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#compareIsLess(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue compareIsLess(IAbstractValue<?> value) {
		return isEqual(value) ? copy() : m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#compareIsGreater(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue compareIsGreater(IAbstractValue<?> value) {
		return isEqual(value) ? copy() : m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#compareIsLessEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue compareIsLessEqual(IAbstractValue<?> value) {
		return isEqual(value) ? copy() : m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#compareIsGreaterEqual(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue compareIsGreaterEqual(IAbstractValue<?> value) {
		return isEqual(value) ? copy() : m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#logicIff(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue logicIff(IAbstractValue<?> value) {
		return m_factory.makeTopValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#logicImplies(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue logicImplies(IAbstractValue<?> value) {
		return m_factory.makeTopValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#logicAnd(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue logicAnd(IAbstractValue<?> value) {
		return m_factory.makeTopValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#logicOr(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue logicOr(IAbstractValue<?> value) {
		return m_factory.makeTopValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#logicNot()
	 */
	@Override
	public TopBottomValue logicNot() {
		return m_factory.makeTopValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#bitVectorConcat(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue bitVectorConcat(IAbstractValue<?> value) {
		return m_factory.makeTopValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue#bitVectorAccess(int, int)
	 */
	@Override
	public TopBottomValue bitVectorAccess(int start, int end) {
		return m_factory.makeTopValue();
	}
	
	public String toString() {
		switch (m_value) {
		case BOTTOM :
			return "BOTTOM";
		case TOP :
			return "TOP";
		default:
			return "ERROR";
		}
	}
}
