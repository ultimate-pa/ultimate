/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces;

/**
 * TODO: Implement!
 * 
 * @author Stefan Wissert
 *
 */
public interface IRating extends Comparable<IRating>{

	/**
	 * TODO: Not sure if this is the right way, to compare with int.
	 * 
	 * @return a rating value as integer
	 */
	public int getRatingAsInteger();
}
