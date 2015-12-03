package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * IAbstractValue stores the value of a variable in an abstract domain.
 * 
 * @author Jan Hättig
 * @author Christopher Dillo
 *
 *
 * @param <T>
 *            Concrete type of the value
 */
public interface IAbstractValue<T> {

	/**
	 * @return The actual value stored in the AbstractValue object
	 */
	public T getValue();

	/**
	 * Return the factory (which can for example create bottom and top elements
	 * for this kind of values)
	 * 
	 * @return
	 */
	public IAbstractValueFactory<?> getFactory();

	/**
	 * @return True iff this value is the top element of its abstract domain
	 */
	public boolean isTop();

	/**
	 * @return True iff this value is the bottom element of its abstract domain
	 */
	public boolean isBottom();

	/**
	 * Returns true, if the value is always true.
	 * 
	 * @return
	 */
	public boolean isTrue();

	/**
	 * Returns true, if the value is can be false.
	 * 
	 * @return
	 */
	public boolean isFalse();

	/**
	 * @return True iff this abstract value represents only one single concrete
	 *         value
	 */
	public boolean representsSingleConcreteValue();

	/**
	 * @return True iff this value is equal to the given value of its abstract
	 *         domain
	 */
	public boolean isEqual(IAbstractValue<?> value);

	/**
	 * @return True iff this value is ordered greater or equal to the given
	 *         value of its abstract domain
	 */
	public boolean isSuperOrEqual(IAbstractValue<?> value);

	/**
	 * @return True iff this value is ordered lesser or equal to the given value
	 *         of its abstract domain
	 */
	public boolean isSub(IAbstractValue<?> value);

	/**
	 * @return A copy of this abstract value
	 */
	public IAbstractValue<T> copy();

	/**
	 * @param value
	 *            The value to add to this value
	 * @return The sum of this value and the given value: this + value <br>
	 *         null if the given abstract state is of an incompatible abstract
	 *         domain system
	 */
	public IAbstractValue<T> add(IAbstractValue<?> value);

	/**
	 * @param value
	 *            The value to subtract from this value
	 * @return The difference of this value and the given value: this - value
	 *         <br>
	 *         null if the given abstract state is of an incompatible abstract
	 *         domain system
	 */
	public IAbstractValue<T> subtract(IAbstractValue<?> value);

	/**
	 * @param value
	 *            The value to multiply with this value
	 * @return The product of this value and the given value: this * value <br>
	 *         If the given abstract state is of an incompatible abstract domain
	 *         system, bottom should be returned
	 */
	public IAbstractValue<T> multiply(IAbstractValue<?> value);

	/**
	 * @param value
	 *            The value to devide this value by
	 * @return The quotient of this value and the given value: this / value <br>
	 *         If the given abstract state is of an incompatible abstract domain
	 *         system, bottom should be returned
	 */
	public IAbstractValue<T> divide(IAbstractValue<?> value);

	/**
	 * @param value
	 *            The value to divide this value by
	 * @return The remainder of this value and the given value: this % value
	 *         <br>
	 *         If the given abstract state is of an incompatible abstract domain
	 *         system, bottom should be returned
	 */
	public IAbstractValue<T> modulo(IAbstractValue<?> value);

	/**
	 * @return The arithmetic negative of this value: -(value)
	 */
	public IAbstractValue<T> negative();

	/**
	 * @param value
	 *            The value to compare this value to (this == value)
	 * @return A value representing the concrete values for which the operation
	 *         returns true, possible over-approximating. Bottom if false for
	 *         all concrete values. <br>
	 *         If the given abstract state is of an incompatible abstract domain
	 *         system, bottom should be returned
	 */
	public IAbstractValue<T> compareIsEqual(IAbstractValue<?> value);

	/**
	 * @param value
	 *            The value to compare this value to (this != value)
	 * @return A value representing the concrete values for which the operation
	 *         returns true, possible over-approximating. Bottom if false for
	 *         all concrete values. <br>
	 *         If the given abstract state is of an incompatible abstract domain
	 *         system, bottom should be returned
	 */
	public IAbstractValue<T> compareIsNotEqual(IAbstractValue<?> value);

	/**
	 * @param value
	 *            The value to compare this value to (this < value)
	 * @return A value representing the concrete values for which the operation
	 *         returns true, possible over-approximating. Bottom if false for
	 *         all concrete values. <br>
	 *         If the given abstract state is of an incompatible abstract domain
	 *         system, bottom should be returned
	 */
	public IAbstractValue<T> compareIsLess(IAbstractValue<?> value);

	/**
	 * @param value
	 *            The value to compare this value to (this > value)
	 * @return A value representing the concrete values for which the operation
	 *         returns true, possible over-approximating. Bottom if false for
	 *         all concrete values. <br>
	 *         If the given abstract state is of an incompatible abstract domain
	 *         system, bottom should be returned
	 */
	public IAbstractValue<T> compareIsGreater(IAbstractValue<?> value);

	/**
	 * @param value
	 *            The value to compare this value to (this <= value)
	 * @return A value representing the concrete values for which the operation
	 *         returns true, possible over-approximating. Bottom if false for
	 *         all concrete values. <br>
	 *         If the given abstract state is of an incompatible abstract domain
	 *         system, bottom should be returned
	 */
	public IAbstractValue<T> compareIsLessEqual(IAbstractValue<?> value);

	/**
	 * @param value
	 *            The value to compare this value to (this >= value)
	 * @return A value representing the concrete values for which the operation
	 *         returns true, possible over-approximating. Bottom if false for
	 *         all concrete values. <br>
	 *         If the given abstract state is of an incompatible abstract domain
	 *         system, bottom should be returned
	 */
	public IAbstractValue<T> compareIsGreaterEqual(IAbstractValue<?> value);

	/**
	 * @param value
	 *            The value to operate with (this <-> value)
	 * @return An abstract value representing the result of the operation
	 */
	public IAbstractValue<T> logicIff(IAbstractValue<?> value);

	/**
	 * @param value
	 *            The value to operate with (this -> value)
	 * @return An abstract value representing the result of the operation
	 */
	public IAbstractValue<T> logicImplies(IAbstractValue<?> value);

	/**
	 * @param value
	 *            The value to operate with (this && value)
	 * @return An abstract value representing the result of the operation
	 */
	public IAbstractValue<T> logicAnd(IAbstractValue<?> value);

	/**
	 * @param value
	 *            The value to operate with (this || value)
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
	 * @return A term representing this abstract value.
	 */
	public Term getTerm(Script script, Term variable);

}
