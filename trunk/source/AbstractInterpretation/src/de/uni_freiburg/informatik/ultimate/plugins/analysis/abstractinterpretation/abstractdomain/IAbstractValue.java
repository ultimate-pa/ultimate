/*
 * Copyright (C) 2014-2015 Christopher Dillo
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AbstractInterpretation plug-in.
 * 
 * The ULTIMATE AbstractInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AbstractInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE AbstractInterpretation plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain;

/**
 * IAbstractValue stores the value of a variable in an abstract domain.
 * 
 * @author Christopher Dillo
 *
 */
public interface IAbstractValue<T> {
	
	/**
	 * @return The actual value stored in the AbstractValue object
	 */
	public T getValue();
	
	/**
	 * @return True iff this value is the top element of its abstract domain
	 */
	public boolean isTop();

	/**
	 * @return True iff this value is the bottom element of its abstract domain
	 */
	public boolean isBottom();
	
	/**
	 * @return True iff this abstract value represents only one single concrete value
	 */
	public boolean representsSingleConcreteValue();

	/**
	 * @return True iff this value is equal to the given value of its abstract domain
	 */
	public boolean isEqual(IAbstractValue<?> value);

	/**
	 * @return True iff this value is ordered greater or equal to the given value of its abstract domain
	 */
	public boolean isSuper(IAbstractValue<?> value);

	/**
	 * @return True iff this value is ordered lesser or equal to the given value of its abstract domain
	 */
	public boolean isSub(IAbstractValue<?> value);
	
	/**
	 * @return A copy of this abstract value
	 */
	public IAbstractValue<T> copy();
	
	/**
	 * @param value The value to add to this value
	 * @return The sum of this value and the given value: this + value
	 * <br> null if the given abstract state is of an incompatible abstract domain system
	 */
	public IAbstractValue<T> add(IAbstractValue<?> value);
	
	/**
	 * @param value The value to subtract from this value
	 * @return The difference of this value and the given value: this - value
	 * <br> null if the given abstract state is of an incompatible abstract domain system
	 */
	public IAbstractValue<T> subtract(IAbstractValue<?> value);

	/**
	 * @param value The value to multiply with this value
	 * @return The product of this value and the given value: this * value
	 * <br> If the given abstract state is of an incompatible abstract domain system, bottom should be returned
	 */
	public IAbstractValue<T> multiply(IAbstractValue<?> value);


	/**
	 * @param value The value to devide this value by
	 * @return The quotient of this value and the given value: this / value
	 * <br> If the given abstract state is of an incompatible abstract domain system, bottom should be returned
	 */
	public IAbstractValue<T> divide(IAbstractValue<?> value);


	/**
	 * @param value The value to divide this value by
	 * @return The remainder of this value and the given value: this % value
	 * <br> If the given abstract state is of an incompatible abstract domain system, bottom should be returned
	 */
	public IAbstractValue<T> modulo(IAbstractValue<?> value);
	
	/**
	 * @return The arithmetic negative of this value: -(value)
	 */
	public IAbstractValue<T> negative();
	
	/**
	 * @param value The value to compare this value to (this == value)
	 * @return A value representing the concrete values for which the operation returns true,
	 * 		possible over-approximating. Bottom if false for all concrete values.
	 * <br> If the given abstract state is of an incompatible abstract domain system, bottom should be returned
	 */
	public IAbstractValue<T> compareIsEqual(IAbstractValue<?> value);
	
	/**
	 * @param value The value to compare this value to (this != value)
	 * @return A value representing the concrete values for which the operation returns true,
	 * 		possible over-approximating. Bottom if false for all concrete values.
	 * <br> If the given abstract state is of an incompatible abstract domain system, bottom should be returned
	 */
	public IAbstractValue<T> compareIsNotEqual(IAbstractValue<?> value);
	
	/**
	 * @param value The value to compare this value to (this < value)
	 * @return A value representing the concrete values for which the operation returns true,
	 * 		possible over-approximating. Bottom if false for all concrete values.
	 * <br> If the given abstract state is of an incompatible abstract domain system, bottom should be returned
	 */
	public IAbstractValue<T> compareIsLess(IAbstractValue<?> value);
	
	/**
	 * @param value The value to compare this value to (this > value)
	 * @return A value representing the concrete values for which the operation returns true,
	 * 		possible over-approximating. Bottom if false for all concrete values.
	 * <br> If the given abstract state is of an incompatible abstract domain system, bottom should be returned
	 */
	public IAbstractValue<T> compareIsGreater(IAbstractValue<?> value);
	
	/**
	 * @param value The value to compare this value to (this <= value)
	 * @return A value representing the concrete values for which the operation returns true,
	 * 		possible over-approximating. Bottom if false for all concrete values.
	 * <br> If the given abstract state is of an incompatible abstract domain system, bottom should be returned
	 */
	public IAbstractValue<T> compareIsLessEqual(IAbstractValue<?> value);
	
	/**
	 * @param value The value to compare this value to (this >= value)
	 * @return A value representing the concrete values for which the operation returns true,
	 * 		possible over-approximating. Bottom if false for all concrete values.
	 * <br> If the given abstract state is of an incompatible abstract domain system, bottom should be returned
	 */
	public IAbstractValue<T> compareIsGreaterEqual(IAbstractValue<?> value);

	/**
	 * @param value The value to operate with (this <-> value)
	 * @return An abstract value representing the result of the operation
	 */
	public IAbstractValue<T> logicIff(IAbstractValue<?> value);

	/**
	 * @param value The value to operate with (this -> value)
	 * @return An abstract value representing the result of the operation
	 */
	public IAbstractValue<T> logicImplies(IAbstractValue<?> value);

	/**
	 * @param value The value to operate with (this && value)
	 * @return An abstract value representing the result of the operation
	 */
	public IAbstractValue<T> logicAnd(IAbstractValue<?> value);

	/**
	 * @param value The value to operate with (this || value)
	 * @return A BoolValue representing the result of the operation
	 */
	public IAbstractValue<T> logicOr(IAbstractValue<?> value);

	/**
	 * @return A BoolValue representing the result of the operation: not value
	 */
	public IAbstractValue<T> logicNot();

	/**
	 * @param value
	 * @return BitVector concatenation of this value and the given value
	 */
	public IAbstractValue<T> bitVectorConcat(IAbstractValue<?> value);

	/**
	 * @param value
	 * @return Part of this BitVector from start to end
	 */
	public IAbstractValue<T> bitVectorAccess(int start, int end);
	
	/**
	 * Called by AbstractState when a value is stored. Enables abstract domains to
	 * get more information about a value, for example at a statement "x := 2 * y"
	 * the resulting abstract value of x could store that it is 2 * y regardless
	 * of the abstract value of y.
	 * @param identifier The identifier of the variable this value object belongs to
	 * @param isGlobal Set to true if the identifier belongs to the global scope,
	 * false if it is a local identifier
	 */
	public void setIdentifier(AbstractState.Pair identifier, boolean isGlobal);
	
	/**
	 * @return A string representation of the abstract value
	 */
	public String toString();
}
