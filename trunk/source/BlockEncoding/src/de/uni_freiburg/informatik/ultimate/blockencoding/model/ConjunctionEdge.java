/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.model;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRating;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.RatingFactory;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.util.EncodingStatistics;

/**
 * This edge represents a conjunction of the formulas of two edges. This is here
 * only virtually, that means we keep here only the references. The "real"
 * conjunction (sequential composition) is done later, when we generate the new
 * minimized graph.
 * 
 * @author Stefan Wissert
 * 
 */
public class ConjunctionEdge extends AbstractCompositeEdge {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * the rating for this Conjunction-Edge
	 */
	protected IRating rating;

	/**
	 * @param left
	 * @param right
	 */
	public ConjunctionEdge(IMinimizedEdge left, IMinimizedEdge right) {
		super(left, right);
		this.payload.setName(leftEdge + " /\\ " + rightEdge);
		this.rating = RatingFactory.getInstance().createRating(this);
		EncodingStatistics
				.setMaxDisjunctionsInOneEdge(this.containedDisjunctions);
	}

	@Override
	public IRating getRating() {
		return rating;
	}

}
