package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain;

import java.util.Map.Entry;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.TypedAbstractVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.*;

/**
 * Superclass of widening and merge operator to prevent copy code
 * 
 * @author GROSS-JAN
 *
 */
public abstract class ValueOperator implements IAbstractOperator<ValueState> {
	protected final IValueOperator<?> mIntOperator;
	protected final IValueOperator<?> mRealOperator;
	protected final IValueOperator<?> mBoolOperator;
	protected final IValueOperator<?> mBitVectorOperator;
	protected final IValueOperator<?> mStringOperator;

	public ValueOperator(IValueOperator<?> intOperator,
			IValueOperator<?> realOperator, IValueOperator<?> boolOperator,
			IValueOperator<?> bitVectorOperator,
			IValueOperator<?> stringOperator) {
		mIntOperator = intOperator;
		mRealOperator = realOperator;
		mBoolOperator = boolOperator;
		mBitVectorOperator = bitVectorOperator;
		mStringOperator = stringOperator;
	}

	/**
	 * Applies the respective operator to each value pair of the given states a
	 * and b. The operators are set in the child class
	 */
	public IAbstractState<ValueState> apply(IAbstractState<ValueState> a,
			IAbstractState<ValueState> b) {
		ValueState vsA = a.getConcrete();
		ValueState vsB = b.getConcrete();
		if (a.isBottom()) {
			return b; // can be bottom as well

		} else if (b.isBottom()) {
			return a;
		}

		// create a new state for the merged values
		ValueState resutlingState = new ValueState(vsA.getDomain(), false);

		// merges each value
		for (Entry<TypedAbstractVariable, IAbstractValue<?>> entry : a
				.getConcrete().getEntries()) {
			TypedAbstractVariable var = entry.getKey();
			IAbstractValue<?> aValue = entry.getValue();
			IAbstractValue<?> bValue = vsB.getValue(var);

			IType type = var.getType();
			if (type instanceof de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType) {
				type = ((de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType) type)
						.getValueType();
			}

			IAbstractValue<?> resultValue = null;
			if (type == BoogieType.boolType) {
				resultValue = mBoolOperator.apply(aValue, bValue);
			} else if (type == BoogieType.intType) {
				resultValue = mIntOperator.apply(aValue, bValue);
			} else if (type == BoogieType.realType) {
				resultValue = mRealOperator.apply(aValue, bValue);
			} else
			// TODO
			{
				throw new NotImplementedException();
			}

			resutlingState.writeValue(var, resultValue);
		}

		// values which are missing in a are considered TOP
		// so it is okay if we do not add them, then they
		// will still be TOP
		// for(Entry<TypedAbstractVariable, IAbstractValue<?>> entry :
		// b.getConcrete().getEntries())
		// {
		// TypedAbstractVariable var = entry.getKey();
		// IAbstractValue<?> aValue = vsA.getValue(var.getString());
		// IAbstractValue<?> bValue = entry.getValue();
		// ...
		// }

		return resutlingState;
	}

	public IValueOperator<?> getIntOperator() {
		return mIntOperator;
	}

	public IValueOperator<?> getRealOperator() {
		return mRealOperator;
	}

	public IValueOperator<?> getBoolOperator() {
		return mBoolOperator;
	}

	public IValueOperator<?> getBitVectorOperator() {
		return mBitVectorOperator;
	}

	public IValueOperator<?> getStringOperator() {
		return mStringOperator;
	}

	@Override
	public String toString() {
		return "operators: " + mIntOperator.toString() + " "
				+ mRealOperator.toString() + " " + mBoolOperator.toString()
				+ " " + mBitVectorOperator.toString() + " "
				+ mStringOperator.toString();
	}
}
