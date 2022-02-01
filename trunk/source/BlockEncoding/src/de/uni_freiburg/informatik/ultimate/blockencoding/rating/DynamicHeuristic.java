/*
 * Copyright (C) 2013-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BlockEncoding plug-in.
 * 
 * The ULTIMATE BlockEncoding plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BlockEncoding plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncoding plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncoding plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BlockEncoding plug-in grant you additional permission 
 * to convey the resulting work.
 */
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

	private final RatingStrategy strategy;

	private final List<RatingStrategy> supportedStrategies;

	private int maxThreshold;

	private int totalRatingValue;

	private int countOfEdges;

	/**
	 * @param strategy
	 */
	public DynamicHeuristic(RatingStrategy strategy) {
		this.strategy = strategy;
		supportedStrategies = new ArrayList<RatingStrategy>();
		supportedStrategies
				.add(RatingStrategy.DISJUNCTIVE_VARIABLES_RATING);
		supportedStrategies
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
		for (final IMinimizedEdge edge : edgeLevel) {
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
		final int newThreshold = (totalRatingValue + totalRating)
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
		for (final IMinimizedEdge checkEdge : edges) {
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
