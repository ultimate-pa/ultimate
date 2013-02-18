package de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.model.structure.IModifiableMultigraphEdge;

/**
 * This interface represents all kinds of minimized edges.
 * 
 * @author Stefan Wissert
 * 
 */
public interface IMinimizedEdge extends IModifiableMultigraphEdge<MinimizedNode, IMinimizedEdge> {

	/**
	 * Is this a basic edge or a composite edge?
	 * 
	 * @return <b>true</b> if it is a basic edge, <br>
	 *         <b>false</b> if it is a composite edge
	 */
	public boolean isBasicEdge();
	
	
	public int getElementCount();
	
}
