/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.rating;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IBasicEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.ICompositeEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IRating;

/**
 * The default rating, simply counts the number of statements which are inside a
 * specific minimized edge.
 * 
 * @author Stefan Wissert
 * 
 */
public class DefaultRating implements IRating {

	private int countOfStatements;

	/**
	 * Constructor, which is only visible in this package (default visibility)
	 * 
	 * @param edge
	 *            the edge to be rated
	 */
	DefaultRating(IMinimizedEdge edge) {
		// Basic-Edges have exactly one statement
		if (edge instanceof IBasicEdge) {
			countOfStatements = 1;
		}
		// For Composite-Edges we summarize the count of statements of the left
		// and the right side
		if (edge instanceof ICompositeEdge) {
			ICompositeEdge compEdge = (ICompositeEdge) edge;
			IMinimizedEdge left = compEdge.getCompositeEdges()[0];
			IMinimizedEdge right = compEdge.getCompositeEdges()[1];
			countOfStatements = left.getRating().getRatingAsInteger()
					+ right.getRating().getRatingAsInteger();
		}
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
		return countOfStatements;
	}

	@Override
	public int compareTo(IRating other) {
		return Integer.valueOf(countOfStatements).compareTo(
				Integer.valueOf(other.getRatingAsInteger()));
	}

}
