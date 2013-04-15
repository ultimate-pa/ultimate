/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.rating;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.DisjunctionEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.ICompositeEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRating;

/**
 * Here we rate an CodeBlock: <br>
 * - BasicEdges := 0; <br>
 * - Conjunction := 0 <br>
 * - Disjunction := 1 <br>
 * So the rated value is the count of the disjunctions inside this formula.
 * 
 * @author Stefan Wissert
 * 
 */
public class DisjunctiveRating implements IRating {

	private RatingValue<Integer> countOfDisjunctions;

	/**
	 * Constructor, which is only visible in this package (default visibility)
	 * 
	 * @param edge
	 *            the edge to be rated
	 */
	DisjunctiveRating(IMinimizedEdge edge) {
		// We only care for composite edges, since basic edge do not contain
		// disjunctions, so there rating = 0
		if (edge instanceof ICompositeEdge) {
			ICompositeEdge compEdge = (ICompositeEdge) edge;
			IMinimizedEdge left = compEdge.getCompositeEdges()[0];
			IMinimizedEdge right = compEdge.getCompositeEdges()[1];
			if (!(left.getRating() instanceof DefaultRating)
					|| !(right.getRating() instanceof DefaultRating)) {
				throw new IllegalArgumentException(
						"Rating-Objects should be of the same type!");
			}
			DefaultRating leftRating = (DefaultRating) left.getRating();
			DefaultRating rightRating = (DefaultRating) right.getRating();
			// Since the underlying edge is a composite, we have to examine the
			// left and the right side of the Disjunction
			countOfDisjunctions = new RatingValue<Integer>(leftRating
					.getRatingValue().getValue()
					+ rightRating.getRatingValue().getValue());
			// if this edge itself is a Disjunction we have to add this
			if (edge instanceof DisjunctionEdge) {
				countOfDisjunctions
						.setValue(countOfDisjunctions.getValue() + 1);
			}
		}

	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Comparable#compareTo(java.lang.Object)
	 */
	@Override
	public int compareTo(IRating other) {
		if (!(other instanceof DisjunctiveRating)) {
			throw new IllegalArgumentException(
					"Comparison of different Ratings is forbidden!");
		}
		return countOfDisjunctions.getValue().compareTo(
				((DisjunctiveRating) other).getRatingValue().getValue());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IRating
	 * #getRatingValue()
	 */
	@Override
	public RatingValue<Integer> getRatingValue() {
		return countOfDisjunctions;
	}

}
