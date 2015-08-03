package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.valuedomain;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.*;

/**
 * Implements the merging of two ValueStates
 * 
 * @author GROSS-JAN
 *
 */
public class ValueMergeOperator implements IAbstractMergeOperator<ValueState>
{
	private static final String s_operatorID = "MERGE_VALUES";
	
	private final IValueMergeOperator<?> mIntMergeOperator;
	private final IValueMergeOperator<?> mRealMergeOperator;
	private final IValueMergeOperator<?> mBoolMergeOperator;
	private final IValueMergeOperator<?> mBitVectorMergeOperator;
	private final IValueMergeOperator<?> mStringMergeOperator;
	
	public ValueMergeOperator(
			IValueMergeOperator<?> intMergeOperator,
			IValueMergeOperator<?> realMergeOperator,
			IValueMergeOperator<?> boolMergeOperator,
			IValueMergeOperator<?> bitVectorMergeOperator,
			IValueMergeOperator<?> stringMergeOperator)
	{
		mIntMergeOperator = intMergeOperator;
		mRealMergeOperator = realMergeOperator;
		mBoolMergeOperator = boolMergeOperator;
		mBitVectorMergeOperator = bitVectorMergeOperator;
		mStringMergeOperator = stringMergeOperator;
	}
	

	public static String getOperatorID()
	{
		return s_operatorID;
	}


	@Override
	public IAbstractState<ValueState> apply(IAbstractState<ValueState> a, IAbstractState<ValueState> b)
	{
		// TODO Auto-generated method stub
		return null;
	}

}
