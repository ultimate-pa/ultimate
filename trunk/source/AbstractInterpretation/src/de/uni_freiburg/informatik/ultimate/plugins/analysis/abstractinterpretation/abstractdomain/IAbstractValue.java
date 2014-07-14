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
public interface IAbstractValue {
	
	/**
	 * @return The unique ID of the abstract domain system the implementing class belongs to
	 */
	public String getDomainID();
	
	/**
	 * @return True iff this value is the top element of its abstract domain
	 */
	public boolean isTop();

	/**
	 * @return True iff this value is the bottom element of its abstract domain
	 */
	public boolean isBottom();

	/**
	 * @return True iff this value is ordered greater or equal to the given value of its abstract domain
	 */
	public boolean isSuper(IAbstractValue value);

	/**
	 * @return True iff this value is ordered lesser or equal to the given value of its abstract domain
	 */
	public boolean isSub(IAbstractValue value);
	
	/**
	 * @return A copy of this abstract value
	 */
	public IAbstractValue copy();
	
	/**
	 * @param value The value to add to this value
	 * @return The sum of this value and the given value: this + value
	 * <br> null if the given abstract state is of an incompatible abstract domain system
	 */
	public IAbstractValue add(IAbstractValue value);
	
	/**
	 * @param value The value to subtract from this value
	 * @return The difference of this value and the given value: this - value
	 * <br> null if the given abstract state is of an incompatible abstract domain system
	 */
	public IAbstractValue subtract(IAbstractValue value);

	/**
	 * @param value The value to multiply with this value
	 * @return The product of this value and the given value: this * value
	 * <br> null if the given abstract state is of an incompatible abstract domain system
	 */
	public IAbstractValue multiply(IAbstractValue value);


	/**
	 * @param value The value to devide this value by
	 * @return The quotient of this value and the given value: this / value
	 * <br> null if the given abstract state is of an incompatible abstract domain system
	 */
	public IAbstractValue divide(IAbstractValue value);


	/**
	 * @param value The value to divide this value by
	 * @return The remainder of this value and the given value: this % value
	 * <br> null if the given abstract state is of an incompatible abstract domain system
	 */
	public IAbstractValue modulo(IAbstractValue value);
	
	/**
	 * @return The arithmetic negative of this value: -(value)
	 */
	public IAbstractValue negative();
	
	/**
	 * @param value The value to compare this value to (this == value)
	 * @return A value representing the concrete values for which the operation returns true,
	 * 		possible over-approximating. Bottom if false for all concrete values.
	 * <br> null if the given abstract state is of an incompatible abstract domain system
	 */
	public IAbstractValue compareIsEqual(IAbstractValue value);
	
	/**
	 * @param value The value to compare this value to (this != value)
	 * @return A value representing the concrete values for which the operation returns true,
	 * 		possible over-approximating. Bottom if false for all concrete values.
	 * <br> null if the given abstract state is of an incompatible abstract domain system
	 */
	public IAbstractValue compareIsNotEqual(IAbstractValue value);
	
	/**
	 * @param value The value to compare this value to (this < value)
	 * @return A value representing the concrete values for which the operation returns true,
	 * 		possible over-approximating. Bottom if false for all concrete values.
	 * <br> null if the given abstract state is of an incompatible abstract domain system
	 */
	public IAbstractValue compareIsLess(IAbstractValue value);
	
	/**
	 * @param value The value to compare this value to (this > value)
	 * @return A value representing the concrete values for which the operation returns true,
	 * 		possible over-approximating. Bottom if false for all concrete values.
	 * <br> null if the given abstract state is of an incompatible abstract domain system
	 */
	public IAbstractValue compareIsGreater(IAbstractValue value);
	
	/**
	 * @param value The value to compare this value to (this <= value)
	 * @return A value representing the concrete values for which the operation returns true,
	 * 		possible over-approximating. Bottom if false for all concrete values.
	 * <br> null if the given abstract state is of an incompatible abstract domain system
	 */
	public IAbstractValue compareIsLessEqual(IAbstractValue value);
	
	/**
	 * @param value The value to compare this value to (this >= value)
	 * @return A value representing the concrete values for which the operation returns true,
	 * 		possible over-approximating. Bottom if false for all concrete values.
	 * <br> null if the given abstract state is of an incompatible abstract domain system
	 */
	public IAbstractValue compareIsGreaterEqual(IAbstractValue value);
}
