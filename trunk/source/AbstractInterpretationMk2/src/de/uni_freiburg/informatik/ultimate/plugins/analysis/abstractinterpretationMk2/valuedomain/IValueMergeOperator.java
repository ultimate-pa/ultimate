/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain;

/**
 * Merge operators of an absract domain system can be used to merge two abstract
 * states while trying not to lose too much precision.
 * 
 * @author Jan Hättig
 *
 */
public interface IValueMergeOperator<T> extends IValueOperator<T> {
	/**
	 * Merges two given values. The order should not matter.
	 * 
	 * @param valueA
	 *            One of the values to merge
	 * @param valueB
	 *            One of the values to merge
	 * @return A merged value which is greater than both given value wrt the
	 *         complete lattice of abstract values
	 */
	public IAbstractValue<T> apply(IAbstractValue<?> valueA,
			IAbstractValue<?> valueB);

	/**
	 * @return A copy of this merge operator
	 */
	public IValueMergeOperator<T> copy();
}
