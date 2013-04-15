/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.rating;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.DisjunctionEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.ICompositeEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRating;

/**
 * Here we store the amount of disjunctions on one edge and additionally store
 * for each disjunction the amount of statements inside.
 * 
 * @author Stefan Wissert
 * 
 */
public class DisjunctiveStatementsRating implements IRating {

	/**
	 * to store the values we use here a Map<DisjunctionEdge, Integer>, so for
	 * every Disjunction (inherited) we count the amount of statements in it.
	 * The size of the determines the amount of disjunctions, in general.
	 */
	private RatingValueContainer<Map<DisjunctionEdge, Integer>> value;

	private int statementBoundary;

	/**
	 * @param edge
	 */
	DisjunctiveStatementsRating(IMinimizedEdge edge) {
		// For Basic-Edges we first initialize our map
		if (edge.isBasicEdge()) {
			value = new RatingValueContainer<Map<DisjunctionEdge, Integer>>(
					new HashMap<DisjunctionEdge, Integer>());
		} else if (edge instanceof ICompositeEdge) {
			// in all other case we should handle ICompositeEdges
			HashMap<DisjunctionEdge, Integer> valueMap = new HashMap<DisjunctionEdge, Integer>();
			ICompositeEdge compEdge = (ICompositeEdge) edge;
			IMinimizedEdge left = compEdge.getCompositeEdges()[0];
			IMinimizedEdge right = compEdge.getCompositeEdges()[1];
			if (!(left.getRating() instanceof DisjunctiveStatementsRating)
					|| !(right.getRating() instanceof DisjunctiveStatementsRating)) {
				throw new IllegalArgumentException(
						"Rating-Objects should be of the same type!");
			}
			// Add the map from the leftSide of the minimized edge
			valueMap.putAll(((DisjunctiveStatementsRating) left.getRating())
					.getRatingValueContainer().getValue());
			// Consequently add the map also from the right
			valueMap.putAll(((DisjunctiveStatementsRating) right.getRating())
					.getRatingValueContainer().getValue());
			// if this edge is also an Disjunction, we have to add it to the map
			if (edge instanceof DisjunctionEdge) {
				valueMap.put((DisjunctionEdge) edge, edge.getElementCount());
			}
			// now we add it to the RatingValue
			value = new RatingValueContainer<Map<DisjunctionEdge, Integer>>(
					valueMap);
		} else {
			throw new IllegalArgumentException(
					"Edge is not BasicEdge neither CompositeEdge");
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Comparable#compareTo(java.lang.Object)
	 */
	@Override
	public int compareTo(IRating other) {
		if (!(other instanceof DisjunctiveStatementsRating)) {
			throw new IllegalArgumentException(
					"Comparison of different Ratings is forbidden!");
		}
		DisjunctiveStatementsRating otherRating = (DisjunctiveStatementsRating) other;
		// to compare we count the disjunctions
		int thisDisjunctions = value.getValue().size();
		int otherDisjunctions = otherRating.getRatingValueContainer()
				.getValue().size();
		// now subtract the amount of statements, which is want
		// (-> statementBoundary)
		for (DisjunctionEdge edge : value.getValue().keySet()) {
			if (value.getValue().get(edge) <= statementBoundary) {
				thisDisjunctions--;
			}
		}
		// now the same for the other side
		for (DisjunctionEdge edge : otherRating.getRatingValueContainer()
				.getValue().keySet()) {
			if (otherRating.getRatingValueContainer().getValue().get(edge) <= statementBoundary) {
				otherDisjunctions--;
			}
		}
		return Integer.valueOf(thisDisjunctions).compareTo(
				Integer.valueOf(otherDisjunctions));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IRating
	 * #getRatingValue()
	 */
	@Override
	public RatingValueContainer<Map<DisjunctionEdge, Integer>> getRatingValueContainer() {
		return value;
	}

	/**
	 * @return the statementBoundary
	 */
	public int getStatementBoundary() {
		return statementBoundary;
	}

	/**
	 * @param statementBoundary
	 *            the statementBoundary to set
	 */
	public void setStatementBoundary(int statementBoundary) {
		this.statementBoundary = statementBoundary;
	}

}
