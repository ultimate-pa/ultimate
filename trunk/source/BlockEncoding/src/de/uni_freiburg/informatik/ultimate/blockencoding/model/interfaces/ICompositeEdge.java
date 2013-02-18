/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces;

/**
 * This interface represents an edge which is composed out of two edges of the
 * type "IMinimizedEdge".
 * 
 * @see IMinimizedEdge
 * 
 * @author Stefan Wissert
 * 
 */
public interface ICompositeEdge extends IMinimizedEdge {

	/**
	 * This method returns the two edges (of type "IMinimizedEdge") of the
	 * composition.
	 * 
	 * @return an array with two composite edges.
	 */
	public IMinimizedEdge[] getCompositeEdges();

	/**
	 * A composite edge is able to check if a other edge, contains already parts
	 * of itself. We need this method to prevent duplication.
	 * 
	 * @param edgeToCheck
	 *            other edge to check
	 * @return true: if there is duplication <br>
	 *         false: if there is no duplication
	 */
	public boolean duplicationOfFormula(IMinimizedEdge edgeToCheck);

}
