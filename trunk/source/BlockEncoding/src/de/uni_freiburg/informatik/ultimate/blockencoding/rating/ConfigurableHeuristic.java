/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.rating;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRating;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRatingHeuristic;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.DefaultRating;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.DisjunctMultiStatementRating;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.DisjunctVariablesRating;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.DisjunctiveRating;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.DisjunctiveStatementsRating;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.UsedVariablesRating;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.RatingFactory.RatingStrategy;

/**
 * Basically this "heuristic" takes the values, which are specified on the
 * preference page.
 * 
 * @author Stefan Wissert
 * 
 */
public class ConfigurableHeuristic implements IRatingHeuristic {

	protected RatingStrategy strategy;

	protected IRating boundary;

	/**
	 * Public constructor needs the used strategy to interpret the given values.
	 * 
	 * @param strategy
	 *            the used RatingStrategy
	 */
	public ConfigurableHeuristic(RatingStrategy strategy) {
		this.strategy = strategy;
	}

	@Override
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
		case USED_VARIABLES_RATING:
			boundary = new UsedVariablesRating(givenPref);
			break;
		case DISJUNCTIVE_VARIABLES_RATING:
			boundary = new DisjunctVariablesRating(givenPref);
			break;
		case DISJUNCTIVE_MULTI_STATEMENT_RATING:
			boundary = new DisjunctMultiStatementRating(givenPref);
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
	public boolean isRatingBoundReached(IRating rating, List<IMinimizedEdge> edgeLevel) {
		if (boundary == null) {
			throw new IllegalArgumentException("No boundary rating specified");
		}
		return rating.compareTo(boundary) <= 0;
	}

	@Override
	public boolean isRatingStrategySupported(RatingStrategy strategy) {
		// here every strategy should be supported!
		return true;
	}

}
