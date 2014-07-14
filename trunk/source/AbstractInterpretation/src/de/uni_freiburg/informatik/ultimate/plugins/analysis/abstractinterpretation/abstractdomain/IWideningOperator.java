/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain;

/**
 * Widening operators of an absract domain system can be used to ensure termination by
 * over-approximating fixed points.
 * 
 * @author Christopher Dillo
 *
 */
public interface IWideningOperator {

	/**
	 * @return The unique ID of the abstract domain system the implementing class belongs to
	 */
	public String getDomainID();
	
	/**
	 * @return A string to identify this widening operator, used for preferences etc
	 */
	public String getName();
	
	/**
	 * Merges two given values while applying widening. The old and new value may not be
	 * treated equally and are thus not interchangable.
	 * @param oldValue The previous abstract value
	 * @param newValue The new abstract value
	 * @return A merged value which is greater than both given value wrt the complete lattice of abstract values
	 */
	public IAbstractValue apply(IAbstractValue oldValue, IAbstractValue newValue);
	
}
