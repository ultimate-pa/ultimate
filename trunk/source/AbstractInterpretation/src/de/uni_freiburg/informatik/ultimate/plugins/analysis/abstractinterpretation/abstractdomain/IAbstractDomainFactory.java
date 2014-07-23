/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain;

/**
 * An AbstractDomainFactory serves to create value, state, widening and merging classes belonging
 * to the same abstract domain system so they can all work together.
 * 
 * @author Christopher Dillo
 *
 */
public interface IAbstractDomainFactory<T> {
	
	/**
	 * @return A new abstract value object with the given value
	 */
	public IAbstractValue<T> makeValue(T value);
	
	/**
	 * @return A new abstract value object representing the top element of the abstract domain
	 */
	public IAbstractValue<T> makeTopValue();
	
	/**
	 * @return A new abstract value object representing the bottom element of the abstract domain
	 */
	public IAbstractValue<T> makeBottomValue();
	
	/**
	 * @param integer Given as a string to support arbitrarily large integers.
	 * @return An abstract value representing the given integer
	 */
	public IAbstractValue<T> makeIntegerValue(String integer);
	
	/**
	 * @param real Given as a string to support arbitrarily large reals.
	 * @return An abstract value representing the given real
	 */
	public IAbstractValue<T> makeRealValue(String real);

	/**
	 * @return A widening operator object corresponding to the choice in the plugin preferences
	 */
	public IWideningOperator<T> getWideningOperator();

	/**
	 * @return A merge operator object corresponding to the choice in the plugin preferences
	 */
	public IMergeOperator<T> getMergeOperator();
	
}
