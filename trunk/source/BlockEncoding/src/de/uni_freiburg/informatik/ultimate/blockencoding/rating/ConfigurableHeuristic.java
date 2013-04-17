/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.rating;

import de.uni_freiburg.informatik.ultimate.blockencoding.rating.RatingFactory.RatingStrategy;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRating;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRatingHeuristic;

/**
 * Basically this "heuristic" takes the values, which are specified on the
 * preference page.
 * 
 * @author Stefan Wissert
 * 
 */
public class ConfigurableHeuristic implements IRatingHeuristic {

	private RatingStrategy strategy;

	private IRating boundary;

	/**
	 * Public constructor needs the used strategy to interpret the given values.
	 * 
	 * @param strategy
	 *            the used RatingStrategy
	 */
	public ConfigurableHeuristic(RatingStrategy strategy) {
		this.strategy = strategy;
	}

	/**
	 * This init-Method should be called before, this heuristic is used!
	 * 
	 * @param givenPref
	 *            the given preference string
	 */
	public void init(String givenPref) {
		// Determine the used strategy
		switch (strategy) {
		case LARGE_BLOCK:
			throw new IllegalArgumentException(
					"For Large Block Encoding, there is no heuristic needed");
		case DEFAULT:
			boundary = new DefaultRating(givenPref);
			break;
		case DISJUNCTIVE_RATING:
			boundary = new DisjunctiveRating(givenPref);
			break;
		case DISJUNCTIVE_STMTCOUNT:
			boundary = new DisjunctiveStatementsRating(givenPref);
			break;
		default:
			throw new IllegalArgumentException(
					"Unkown state of the enum RatingStrategy,"
							+ " need to place all possibilites here!");
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.
	 * IRatingHeuristic
	 * #isRatingBoundReached(de.uni_freiburg.informatik.ultimate.
	 * blockencoding.rating.interfaces.IRating)
	 */
	@Override
	public boolean isRatingBoundReached(IRating rating) {
		if (boundary == null) {
			throw new IllegalArgumentException("No boundary rating specified");
		}
		return rating.compareTo(boundary) <= 0;
	}

}
