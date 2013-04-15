/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.rating;

/**
 * This generic container class, stores the value of the computed rating. It can
 * be used for comparison and further analysis.
 * 
 * @author Stefan Wissert
 * 
 */
public class RatingValue<T> {

	/**
	 * the generic value.
	 */
	private T value;

	/**
	 * Constructor of the container class.
	 * 
	 * @param value the generic value.
	 */
	public RatingValue(T value) {
		this.value = value;
	}

	/**
	 * @return the generic value
	 */
	public T getValue() {
		return value;
	}

	/**
	 * @param value
	 */
	public void setValue(T value) {
		this.value = value;
	}
}
