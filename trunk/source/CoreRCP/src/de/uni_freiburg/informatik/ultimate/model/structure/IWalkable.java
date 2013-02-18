package de.uni_freiburg.informatik.ultimate.model.structure;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.access.walker.IWalker;
import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.INode;

/***
 * This interface is a temporary bridge between old ({@link INode},{@link IEdge}
 * ) and new ({@link ISimpleAST}, {@link IDirectedGraph},
 * {@link ILabeledEdgesMultigraph}, {@link IExplicitEdgesMultigraph}) data
 * structures. It allows the Core to traverse those structures and continue the
 * use of the {@link IWalker} and {@link IObserver} infrastructure.
 * 
 * @author dietsch
 * 
 */
public interface IWalkable extends IElement {

	/***
	 * This method returns a list of successors of the current node.
	 * 
	 * This method may not return null.
	 * 
	 * @return A list of successors or an empty list.
	 */
	List<IWalkable> getSuccessors();
}
