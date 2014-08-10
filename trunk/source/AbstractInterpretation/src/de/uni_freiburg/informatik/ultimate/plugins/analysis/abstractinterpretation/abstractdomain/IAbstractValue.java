/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain;

/**
 * IAbstractValue stores the value of a variable in an abstract dromain.
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
	 * @return A string representation of the abstract value
	 */
	public String toString();
}
