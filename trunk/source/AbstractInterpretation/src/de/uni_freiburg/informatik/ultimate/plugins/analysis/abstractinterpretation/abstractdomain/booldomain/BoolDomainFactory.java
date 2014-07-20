/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.booldomain;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.booldomain.BoolValue.Bool;

/**
 * @author Christopher Dillo
 *
 */
public class BoolDomainFactory implements IAbstractDomainFactory {

	public static final String s_DomainID = "BOOL";

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#getDomainID()
	 */
	@Override
	public String getDomainID() {
		return s_DomainID;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeTopValue()
	 */
	@Override
	public BoolValue makeTopValue() {
		return new BoolValue(Bool.UNKNOWN);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeBottomValue()
	 */
	@Override
	public BoolValue makeBottomValue() {
		return new BoolValue(Bool.EMPTY);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeIntegerValue(java.lang.String)
	 */
	@Override
	public BoolValue makeIntegerValue(String integer) {
		if (integer == "0") return new BoolValue(Bool.FALSE); // TODO: proper int string handling
		return new BoolValue(Bool.TRUE);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeRealValue(java.lang.String)
	 */
	@Override
	public BoolValue makeRealValue(String real) {
		if (real == "0") return new BoolValue(Bool.FALSE); // TODO: proper real string handling
		return new BoolValue(Bool.TRUE);
	}
	
	/**
	 * @param bool
	 * @return A BoolValue based on a given boolean value (true or false)
	 */
	public BoolValue makeBooleanValue(boolean bool) {
		return new BoolValue(bool ? Bool.TRUE : Bool.FALSE);
	}
	
	/**
	 * For use with values generated from IAbstractValue's comparison operators
	 * @param value An abstract value to get a boolean value for
	 * @return A copy of the value if it is a BoolValue, otherwise FALSE, if the given value is bottom; else true
	 */
	public BoolValue makeFromAbstractValue(IAbstractValue value) {
		if (value instanceof BoolValue) return (BoolValue) value.copy();
		
		return new BoolValue(value.isBottom() ? Bool.FALSE : Bool.TRUE);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeWideningOperator()
	 */
	@Override
	public IWideningOperator makeWideningOperator() {
		return new BoolMergeWideningOperator();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeMergeOperator()
	 */
	@Override
	public IMergeOperator makeMergeOperator() {
		return new BoolMergeWideningOperator();
	}

}
