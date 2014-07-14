/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain;

/**
 * Merge operators of an absract domain system can be used to merge two abstract states
 * while trying not to lose too much precision.
 * 
 * @author Christopher Dillo
 *
 */
public interface IMergeOperator {

	/**
	 * @return The unique ID of the abstract domain system the implementing class belongs to
	 */
	public String getDomainID();
	
	/**
	 * @return A string to identify this merge operator, used for preferences etc
	 */
	public String getName();
	
	/**
	 * Merges two given values. The order should not matter.
	 * @param valueA One of the values to merge
	 * @param valueB One of the values to merge
	 * @return A merged value which is greater than both given value wrt the complete lattice of abstract values
	 */
	public IAbstractValue apply(IAbstractValue valueA, IAbstractValue valueB);
	
}
