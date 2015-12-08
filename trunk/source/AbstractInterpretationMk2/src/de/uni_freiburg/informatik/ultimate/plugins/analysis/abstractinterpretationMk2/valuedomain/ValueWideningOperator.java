package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.*;

/**
 * Implements the merging of two ValueStates
 * 
 * @author GROSS-JAN
 *
 */
public class ValueWideningOperator extends ValueOperator implements
		IAbstractWideningOperator<ValueState> {
	private static final String s_operatorID = "WIDEN_VALUES";

	public ValueWideningOperator(IValueWideningOperator<?> intWideningOperator,
			IValueWideningOperator<?> realWideningOperator,
			IValueWideningOperator<?> boolWideningOperator,
			IValueWideningOperator<?> bitVectorWideningOperator,
			IValueWideningOperator<?> stringWideningOperator) {
		// pass the merge operators to the super class
		// the super class will apply them on any given states
		super(intWideningOperator, realWideningOperator, boolWideningOperator,
				bitVectorWideningOperator, stringWideningOperator);
	}

	public static String getOperatorID() {
		return s_operatorID;
	}

	@Override
	public String toString() {
		return s_operatorID + super.toString();
	}
}
