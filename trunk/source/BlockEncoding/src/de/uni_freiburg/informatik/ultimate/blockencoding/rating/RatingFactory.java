/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.rating;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRating;

/**
 * Factory class to create ratings for the edges in the minimized CFG. There
 * will be different strategies how to create such a rating, the only valid way
 * for creation is this class.
 * 
 * @author Stefan Wissert
 * 
 */
public class RatingFactory {

	/**
	 * This enumeration specifies the RatingStrategy. It can be set in the
	 * preferences. Every new strategy has to be declared here.
	 */
	public static enum RatingStrategy {
		/**
		 * use large block encoding, there is no special rating
		 */
		LARGE_BLOCK,
		/**
		 * The default strategy, is to count the statements.
		 */
		DEFAULT,
		/**
		 * This strategy counts the amount of disjunctions.
		 */
		DISJUNCTIVE_RATING,
		/**
		 * Here we count the disjunctive in context of the amount of statements
		 * which is inherited inside the disjunctions.
		 */
		DISJUNCTIVE_STMTCOUNT
	}

	/**
	 * there is only one instance of this factory
	 */
	private static RatingFactory instance;

	/**
	 * 
	 */
	private RatingStrategy strategy;

	/**
	 * We do not allow to create instances of this class.
	 */
	private RatingFactory() {
		this.strategy = RatingFactory.RatingStrategy.DEFAULT;
	}

	/**
	 * Returns the instance of this factory.
	 * 
	 * @return the only existing instance of RatingFactory
	 */
	public static RatingFactory getInstance() {
		if (instance == null) {
			instance = new RatingFactory();
		}
		return instance;
	}

	/**
	 * Setting up the strategy for rating of the edges.
	 * 
	 * @param value
	 *            the preference value
	 */
	public void setRatingStrategy(String value) {
		try {
			strategy = RatingStrategy.values()[Integer.parseInt(value)];
		} catch (NumberFormatException e) {
			throw new IllegalArgumentException(
					"There is something wrong, with the enum setup");
		}
	}

	/**
	 * Creates a rating for a given minimized edge. In order to do this, there
	 * are different strategies (which can be set, via the preferences).
	 * 
	 * @param edge
	 *            the minimized edge, which we want to rate
	 * @return the created rating for the minimized edge
	 */
	public IRating createRating(IMinimizedEdge edge) {
		switch (strategy) {
		case LARGE_BLOCK:
		case DEFAULT:
			return new DefaultRating(edge);
		case DISJUNCTIVE_RATING:
			return new DisjunctiveRating(edge);
		case DISJUNCTIVE_STMTCOUNT:
			return new DisjunctiveStatementsRating(edge);
		default:
			throw new IllegalArgumentException("No valid strategy choosen!");
		}
	}
}
