/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.model;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;

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
	 * @param left
	 * @param right
	 */
	public ConjunctionEdge(IMinimizedEdge left, IMinimizedEdge right) {
		super(left, right);
		this.payload.setName(leftEdge + " /\\ " + rightEdge);
	}

}
