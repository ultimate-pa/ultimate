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
public interface IAbstractDomainFactory {

	/**
	 * @return The unique ID of the abstract domain system the implementing class belongs to
	 */
	public String getDomainID();
	
	/**
	 * @return A new abstract value object representing the top element of the abstract domain
	 */
	public IAbstractValue makeTopValue();
	
	/**
	 * @return A new abstract value object representing the bottom element of the abstract domain
	 */
	public IAbstractValue makeBottomValue();
	
	/**
	 * @param integer Given as a string to support arbitrarily large integers.
	 * @return An abstract value representing the given integer
	 */
	public IAbstractValue makeIntegerValue(String integer);
	
	/**
	 * @param real Given as a string to support arbitrarily large reals.
	 * @return An abstract value representing the given real
	 */
	public IAbstractValue makeRealValue(String real);

	/**
	 * @return A widening operator object corresponding to the choice in the plugin preferences
	 */
	public IWideningOperator makeWideningOperator();

	/**
	 * @return A merge operator object corresponding to the choice in the plugin preferences
	 */
	public IMergeOperator makeMergeOperator();
	
}
