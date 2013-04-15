/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces;

/**
 * Basically classes which implement this interface define a certain boundary
 * for which we take another rated edge level. The main target is, that this
 * boundary is automatically defined (computed) so that no user input should be
 * given. Another way is that the use can specify a certain boundary.
 * 
 * @author Stefan Wissert
 * 
 */
public interface IRatingHeuristic {

	/**
	 * This method determines, if the certain boundary, defined by this
	 * heuristic, is reached.
	 * 
	 * @param rating
	 *            the Rating to check
	 * @return <b>true</b>, when we are less than or equal to the boundary value <br>
	 *         <b>false</b>, if the boundary is not reached <br>
	 */
	public boolean isRatingBoundReached(IRating rating);

}
