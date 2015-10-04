package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractMergeOperator;

/**
 * Implements the merging of two ValueStates
 * 
 * @author GROSS-JAN
 *
 */
public class ValueMergeOperator extends ValueOperator implements
		IAbstractMergeOperator<ValueState> {
	private static final String s_operatorID = "MERGE_VALUES";

	public ValueMergeOperator(IValueMergeOperator<?> intMergeOperator,
			IValueMergeOperator<?> realMergeOperator,
			IValueMergeOperator<?> boolMergeOperator,
			IValueMergeOperator<?> bitVectorMergeOperator,
			IValueMergeOperator<?> stringMergeOperator) {
		// pass the merge operators to the super class
		// the super class will apply them on any given states
		super(intMergeOperator, realMergeOperator, boolMergeOperator,
				bitVectorMergeOperator, stringMergeOperator);
	}

	public static String getOperatorID() {
		return s_operatorID;
	}

	@Override
	public String toString() {
		return s_operatorID + super.toString();
	}
}
