/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.RatingFactory.RatingStrategy;

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
	public boolean isRatingBoundReached(IRating rating, List<IMinimizedEdge> edgeLevel);

	/**
	 * The heuristic can be initialized with a preference value which can be
	 * determined in the global preferences of the plugin.
	 * 
	 * @param givenPref
	 *            the preference value as String
	 */
	public void init(String givenPref);
	
	
	/**
	 * Determines if there is a heuristic support for the chosen rating strategy.
	 * 
	 * @param strategy the chosen strategy
	 * @return <b>true</b>, if the strategy is supported <br>
	 *         <b>false</b>, otherwise <br>
	 */
	public boolean isRatingStrategySupported(RatingStrategy strategy);

}
