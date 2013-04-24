package de.uni_freiburg.informatik.ultimate.blockencoding.model;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.RatingFactory;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRating;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.util.EncodingStatistics;

/**
 * This edge represents a disjunction of the formulas of two edges. This is here
 * only virtually, that means we keep here only the references. The "real"
 * disjunction (parallel composition) is done later, when we generate the new
 * minimized graph.
 * 
 * @author Stefan Wissert
 * 
 */
public class DisjunctionEdge extends AbstractCompositeEdge {

	/**
	 * Serial number, do not really use it.
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * the rating for this Disjunction-Edge
	 */
	private IRating rating;

	/**
	 * @param left
	 * @param right
	 */
	public DisjunctionEdge(IMinimizedEdge left, IMinimizedEdge right) {
		super(left, right);
		this.containedDisjunctions++;
		this.payload.setName(leftEdge + " V " + rightEdge);
		this.rating = RatingFactory.getInstance().createRating(this);
		EncodingStatistics.incCountOfDisjunctions();
		EncodingStatistics
				.setMaxDisjunctionsInOneEdge(this.containedDisjunctions);
		EncodingStatistics.setMaxElementsInOneDisjunction(this
				.getElementCount());
	}

	/**
	 * Empty constructor, is needed to create edges for rating boundary
	 */
	public DisjunctionEdge() {

	}

	@Override
	public IRating getRating() {
		return rating;
	}
}
