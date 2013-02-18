package de.uni_freiburg.informatik.ultimate.model.structure;

import de.uni_freiburg.informatik.ultimate.ep.interfaces.IOutput;

/***
 * This interface describes structures that can be visualized by an
 * {@link IOutput} plugin. Only root elements of graphs need to implement this
 * interface, i.e. edges are not necessary. For more information, see
 * {@link VisualizationNode}.
 * 
 * @author dietsch
 * @see VisualizationNode
 */
public interface IVisualizable {

	/***
	 * This method returns a {@link VisualizationNode} of the current graph
	 * node. This node can be used to create a new graph structure for
	 * {@link IOutput} plugins, so that they only need to consider one graph
	 * structure.
	 * 
	 * Clients can call this method on the root element of a graph and the
	 * traverse the resulting directed multigraph. See {@link VisualizationNode}
	 * for more information.
	 * 
	 * @return A representation of the current graph node as
	 *         {@link VisualizationNode}.
	 */
	VisualizationNode getVisualizationGraph();

}
