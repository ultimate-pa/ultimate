/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.rating;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IRating;

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
		 * The default strategy, is to count the statements.
		 */
		DEFAULT
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
	 * Creates a rating for a given minimized edge. In order to do this, there
	 * are different strategies (which can be set, via the preferences).
	 * 
	 * @param edge
	 *            the minimized edge, which we want to rate
	 * @return the created rating for the minimized edge
	 */
	public IRating createRating(IMinimizedEdge edge) {
		switch (strategy) {
		case DEFAULT:
			return new DefaultRating(edge);
		default:
			throw new IllegalArgumentException("No valid strategy choosen!");
		}
	}
}
