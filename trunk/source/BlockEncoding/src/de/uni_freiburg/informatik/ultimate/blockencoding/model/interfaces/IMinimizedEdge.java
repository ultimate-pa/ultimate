package de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRating;
import de.uni_freiburg.informatik.ultimate.model.structure.IModifiableMultigraphEdge;

/**
 * This interface represents all kinds of minimized edges.
 * 
 * @author Stefan Wissert
 * 
 */
public interface IMinimizedEdge extends
		IModifiableMultigraphEdge<MinimizedNode, IMinimizedEdge> {

	/**
	 * Is this a basic edge or a composite edge?
	 * 
	 * @return <b>true</b> if it is a basic edge, <br>
	 *         <b>false</b> if it is a composite edge
	 */
	public boolean isBasicEdge();

	/**
	 * Since there is an unsolved problem to minimize Call- and Return-Edges
	 * with SequentialComposition which the "old(...)"-Expression is contained,
	 * we check edges if this expression is involved. If this is the case we do
	 * not allow the minimization of Call-Edges in this case.
	 * 
	 * @return <b>true</b> if old is used, <br>
	 *         <b>false</b> if old is not used
	 */
	public boolean isOldVarInvolved();

	/**
	 * Every edge in the minimized model is rated with some metrics
	 * (complexity). So that we are now able to control which edges we want, and
	 * which we do not want. This is maybe needed because Large Block Encoding
	 * does to much minimization.
	 * 
	 * @return the computed Rating of this edge.
	 */
	public IRating getRating();

	public int getElementCount();

}
