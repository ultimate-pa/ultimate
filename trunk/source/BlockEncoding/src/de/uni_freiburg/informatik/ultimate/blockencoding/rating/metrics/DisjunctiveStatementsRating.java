/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.DisjunctionEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.ICompositeEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.RatingValueContainer;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRating;

/**
 * Here we store the amount of disjunctions on one edge and additionally store
 * for each disjunction the amount of statements inside. <br>
 * We can compare these ratings, since we implement Comparable. The logic is
 * that we do not count disjunctions, which have an amount of elements which
 * under a certain boundary. In addition we rate disjunctions which are over a
 * certain amount twice as high.
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

	/**
	 * the under bound.
	 */
	private int underStmtBound;

	/**
	 * the higher bound.
	 */
	private int upperStmtBound;

	/**
	 * @param edge
	 */
	DisjunctiveStatementsRating(IMinimizedEdge edge) {
		this.underStmtBound = Integer.MIN_VALUE;
		this.upperStmtBound = Integer.MAX_VALUE;
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

	/**
	 * Constructor which is used to create an boundary rating for the heuristic.
	 * 
	 * @param prefValue
	 *            the preference value
	 */
	public DisjunctiveStatementsRating(String prefValue) {
		// Here the preference string should have the following format
		// #Disjunctions|underBoundary|upperBoundary
		String[] prefs = prefValue.split("-");
		if (prefs.length != 3) {
			throw new IllegalArgumentException("Preference String should"
					+ " contain exactly three items!");
		}
		int countOfDisjunctions = Integer.parseInt(prefs[0]);
		this.underStmtBound = Integer.parseInt(prefs[1]);
		this.upperStmtBound = Integer.parseInt(prefs[2]);
		// we initialize the map with the amount of disjunctions, we specified
		// before in the preferences, for statement counts, we take
		// (underStmtBound + upperStmtBound) / 2
		HashMap<DisjunctionEdge, Integer> fakeMap = new HashMap<DisjunctionEdge, Integer>();
		for (int i = 0; i < countOfDisjunctions; i++) {
			fakeMap.put(new DisjunctionEdge(),
					((underStmtBound + upperStmtBound) / 2));
		}
		this.value = new RatingValueContainer<Map<DisjunctionEdge, Integer>>(
				fakeMap);
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
		// first we have to set under and upper boundary for contained statements
		if (otherRating.getUnderStmtBound() != Integer.MIN_VALUE) {
			this.underStmtBound = otherRating.getUnderStmtBound();
		}
		if (otherRating.getUpperStmtBound() != Integer.MAX_VALUE) {
			this.upperStmtBound = otherRating.getUpperStmtBound();
		}
		// to compare we count the disjunctions
		int thisDisjunctions = value.getValue().size();
		int otherDisjunctions = otherRating.getRatingValueContainer()
				.getValue().size();
		// value - 1, if stmtCount <= underStmtBound
		// value + 1, if stmtCount > upperStmtBound
		for (DisjunctionEdge edge : value.getValue().keySet()) {
			if (value.getValue().get(edge) <= underStmtBound) {
				thisDisjunctions--;
			} else if (value.getValue().get(edge) > upperStmtBound) {
				thisDisjunctions++;
			}
		}
		// now the same for the other side
		for (DisjunctionEdge edge : otherRating.getRatingValueContainer()
				.getValue().keySet()) {
			if (otherRating.getRatingValueContainer().getValue().get(edge) <= underStmtBound) {
				otherDisjunctions--;
			} else if (otherRating.getRatingValueContainer().getValue()
					.get(edge) > upperStmtBound) {
				otherDisjunctions++;
			}
		}
		// we compare simply the count of disjunctions, according our logic
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
	 * @return the undertStmtBound
	 */
	public int getUnderStmtBound() {
		return underStmtBound;
	}

	/**
	 * @param underStmtBound
	 *            the underStmtBound to set
	 */
	public void setUnderStmtBound(int underStmtBound) {
		this.underStmtBound = underStmtBound;
	}

	/**
	 * @return the upperStmtBound
	 */
	public int getUpperStmtBound() {
		return upperStmtBound;
	}

	/**
	 * @param upperStmtBound
	 *            the upperStmtBound to set
	 */
	public void setUpperStmtBound(int upperStmtBound) {
		this.upperStmtBound = upperStmtBound;
	}

	@Override
	public int getRatingValueAsInteger() {
		return value.getValue().size();
	}

}
