/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.RatingValueContainer;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRating;

/**
 * In this rating we count the number of used variables, this may be an
 * interesting value to measure the complexity of single formulas.
 * 
 * @author Stefan Wissert
 * 
 */
public class UsedVariablesRating implements IRating {

	private RatingValueContainer<Integer> countUsedVariables;

	/**
	 * Constructor, which is only visible in this package (default visibility)
	 * 
	 * @param edge
	 *            , the edge to be rated
	 */
	UsedVariablesRating(IMinimizedEdge edge) {
		countUsedVariables = new RatingValueContainer<Integer>(edge
				.getDifferentVariables().size());
	}

	/**
	 * Constructor to create a rating boundary for the heuristic, visibility is
	 * default (package)
	 * 
	 * @param value
	 *            the preference value
	 */
	public UsedVariablesRating(String prefValue) {
		countUsedVariables = new RatingValueContainer<Integer>(
				Integer.parseInt(prefValue));
	}
	
	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Comparable#compareTo(java.lang.Object)
	 */
	@Override
	public int compareTo(IRating other) {
		if (!(other instanceof UsedVariablesRating)) {
			throw new IllegalArgumentException(
					"Comparison of different Ratings is forbidden!");
		}
		return countUsedVariables.getValue().compareTo(
				((UsedVariablesRating) other).getRatingValueContainer()
						.getValue());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRating
	 * #getRatingValueContainer()
	 */
	@Override
	public RatingValueContainer<Integer> getRatingValueContainer() {
		return countUsedVariables;
	}

	@Override
	public int getRatingValueAsInteger() {
		return countUsedVariables.getValue();
	}

}
