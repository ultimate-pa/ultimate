/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.DisjunctionEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.ICompositeEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.RatingValueContainer;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRating;

/**
 * This metric is basically a mixture between counting Disjunctions and the
 * Statements in one Edge. <br>
 * So we count here the disjunctions (inherited in the edge) and the number of
 * statements used. Every edge has the following rating formula: <br>
 * Value = Count of Disjunctions * Count of Statements
 * 
 * @author Stefan Wissert
 * 
 */
public class DisjunctMultiStatementRating implements IRating {

	/**
	 * The inherited integer array has exactly three values inside: <br>
	 * 1. number of disjunctions <br>
	 * 2. number of counted statements <br>
	 * 3. the computed rating value
	 */
	private RatingValueContainer<Integer[]> ratingValue;

	/**
	 * Constructor with default visibility, is only used in the factory.
	 * 
	 * @param edge
	 *            the IMinimizedEdge to rate
	 */
	DisjunctMultiStatementRating(IMinimizedEdge edge) {
		if (edge.isBasicEdge()) {
			ratingValue = new RatingValueContainer<Integer[]>(new Integer[] {
					0, edge.getElementCount(), edge.getElementCount() });
		} else {
			if (!(edge instanceof ICompositeEdge)) {
				throw new IllegalArgumentException(
						"There should be an CompositeEdge here!");
			}
			IMinimizedEdge[] edges = ((ICompositeEdge) edge)
					.getCompositeEdges();
			int totalDisjunctions = 0;
			int totalStatements = 0;
			int computedRating = 0;
			for (IMinimizedEdge compEdge : edges) {
				Integer[] ratingValues = (Integer[]) compEdge.getRating()
						.getRatingValueContainer().getValue();
				totalDisjunctions = totalDisjunctions + ratingValues[0];
				totalStatements = totalStatements + ratingValues[1];
			}
			// if the actual edge is a disjunction we add this to the total
			// disjunctions (otherwise it stays the computed value)
			if (edge instanceof DisjunctionEdge) {
				totalDisjunctions++;
			}

			if (totalDisjunctions == 0) {
				computedRating = totalStatements;
			} else {
				// so for 1 Disjunction we multiply by 2 and for 2 we multiply
				// by 3 (and so on)
				computedRating = (totalDisjunctions + 1) * totalStatements;
			}
			ratingValue = new RatingValueContainer<Integer[]>(new Integer[] {
					totalDisjunctions, totalStatements, computedRating });
		}
	}

	/**
	 * Constructor, to create a rating boundary.
	 * 
	 * @param prefValue
	 *            only the rating value, disjunctions or statements doesn't
	 *            matter
	 */
	public DisjunctMultiStatementRating(String prefValue) {
		ratingValue = new RatingValueContainer<Integer[]>(new Integer[] { 0, 0,
				Integer.parseInt(prefValue) });
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Comparable#compareTo(java.lang.Object)
	 */
	@Override
	public int compareTo(IRating other) {
		if (!(other instanceof DisjunctMultiStatementRating)) {
			throw new IllegalArgumentException(
					"Comparison of different Ratings is forbidden!");
		}
		Integer[] values = ((DisjunctMultiStatementRating) other)
				.getRatingValueContainer().getValue();
		return ratingValue.getValue()[2].compareTo(values[2]);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRating
	 * #getRatingValueContainer()
	 */
	@Override
	public RatingValueContainer<Integer[]> getRatingValueContainer() {
		return ratingValue;
	}

	@Override
	public int getRatingValueAsInteger() {
		return ratingValue.getValue()[2];
	}

}
