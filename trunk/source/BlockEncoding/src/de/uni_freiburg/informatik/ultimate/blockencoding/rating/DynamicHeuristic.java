/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.rating;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IBasicEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRating;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRatingHeuristic;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.RatingFactory.RatingStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;

/**
 * The basic idea behind this heuristic is to compute, while converting, a
 * average rating value per edge. Per preference we store some maximum
 * threshold, which should not be reached anyway.
 * 
 * @author Stefan Wissert
 * 
 */
public class DynamicHeuristic implements IRatingHeuristic {

	private RatingStrategy strategy;

	private List<RatingStrategy> supportedStrategies;

	private int maxThreshold;

	private int totalRatingValue;

	private int countOfEdges;

	/**
	 * @param strategy
	 */
	public DynamicHeuristic(RatingStrategy strategy) {
		this.strategy = strategy;
		this.supportedStrategies = new ArrayList<RatingStrategy>();
		this.supportedStrategies
				.add(RatingStrategy.DISJUNCTIVE_VARIABLES_RATING);
		this.supportedStrategies
				.add(RatingStrategy.DISJUNCTIVE_MULTI_STATEMENT_RATING);
	}

	@Override
	public void init(String givenPref) {
		maxThreshold = Integer.parseInt(givenPref);
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
	public boolean isRatingBoundReached(IRating rating,
			List<IMinimizedEdge> edgeLevel) {
		if (!supportedStrategies.contains(strategy)) {
			throw new IllegalArgumentException("Illegal Strategy chosen!");
		}
		int totalRating = 0;
		int edges = 0;
		MinimizedNode source = null;
		for (IMinimizedEdge edge : edgeLevel) {
			if (source == null) {
				source = edge.getSource();
			}
			totalRating += edge.getRating().getRatingValueAsInteger();
			edges++;
		}

		if (source != null) {
			if (source.getIncomingEdges() == null
					|| source.getIncomingEdges().isEmpty()
					|| containsOnlyCalls(edgeLevel)) {
				// we take all edges which begin at an entry node
				// (other idea, is to do the same with the same to all edges
				// which end in error location)
				countOfEdges += edges;
				return true;
			}
		}
		// here we compute what the new average value would be
		int newThreshold = (totalRatingValue + totalRating)
				/ (countOfEdges + edges);
		// now check if the new threshold is under the maximum given there
		if (newThreshold <= maxThreshold) {
			// so everything is all right, we can take this edge level
			totalRatingValue += totalRating;
			countOfEdges += edges;
			return true;
		}
		return false;
	}

	private boolean containsOnlyCalls(List<IMinimizedEdge> edges) {
		for (IMinimizedEdge checkEdge : edges) {
			if (!(checkEdge.isBasicEdge())) {
				return false;
			} else {
				if (!(((IBasicEdge) checkEdge).getOriginalEdge() instanceof Call)) {
					return false;
				}
			}
		}
		return true;
	}

	@Override
	public boolean isRatingStrategySupported(RatingStrategy strategy) {
		return supportedStrategies.contains(strategy);
	}
}
