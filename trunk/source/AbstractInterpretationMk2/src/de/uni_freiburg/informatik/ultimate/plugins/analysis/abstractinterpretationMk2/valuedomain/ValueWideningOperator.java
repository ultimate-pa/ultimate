package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.*;

/**
 * Implements the merging of two ValueStates
 * 
 * @author GROSS-JAN
 *
 */
public class ValueWideningOperator implements IAbstractWideningOperator<ValueState>
{
	private static final String s_operatorID = "WIDEN_VALUES";
	
	private final IValueWideningOperator<?> mIntWideningOperator;
	private final IValueWideningOperator<?> mRealWideningOperator;
	private final IValueWideningOperator<?> mBoolWideningOperator;
	private final IValueWideningOperator<?> mBitVectorWideningOperator;
	private final IValueWideningOperator<?> mStringWideningOperator;
	
	public ValueWideningOperator(
			IValueWideningOperator<?> intWideningOperator,
			IValueWideningOperator<?> realWideningOperator,
			IValueWideningOperator<?> boolWideningOperator,
			IValueWideningOperator<?> bitVectorWideningOperator,
			IValueWideningOperator<?> stringWideningOperator)
	{
		mIntWideningOperator = intWideningOperator;
		mRealWideningOperator = realWideningOperator;
		mBoolWideningOperator = boolWideningOperator;
		mBitVectorWideningOperator = bitVectorWideningOperator;
		mStringWideningOperator = stringWideningOperator;
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
