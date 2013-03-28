/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.rating;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.DisjunctionEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.ICompositeEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IRating;

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

	private int countOfDisjunctions;

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
			// Since the underlying edge is a composite, we have to examine the
			// left and the right side of the Disjunction
			countOfDisjunctions = left.getRating().getRatingAsInteger()
					+ right.getRating().getRatingAsInteger();
			// if this edge itself is a Disjunction we have to add this
			if (edge instanceof DisjunctionEdge) {
				countOfDisjunctions++;
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
		return Integer.valueOf(countOfDisjunctions).compareTo(
				Integer.valueOf(other.getRatingAsInteger()));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IRating
	 * #getRatingAsInteger()
	 */
	@Override
	public int getRatingAsInteger() {
		return countOfDisjunctions;
	}

}
