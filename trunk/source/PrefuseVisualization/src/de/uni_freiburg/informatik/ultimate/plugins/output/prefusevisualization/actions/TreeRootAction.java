package de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.actions;

import java.util.Iterator;

import prefuse.Visualization;
import prefuse.action.GroupAction;
import prefuse.data.Graph;
import prefuse.data.Node;
import prefuse.data.tuple.TupleSet;

/**
 * Switch the root of the tree by requesting a new spanning tree at the desired
 * root
 *
 * @author keil
 * @version 0.0.1 
 * $LastChangedDate$
 * $LastChangedBy$
 * $LastChangedRevision$
 */
public class TreeRootAction extends GroupAction {
	public TreeRootAction(String graphGroup) {
		super(graphGroup);
	}

	/* (non-Javadoc)
	 * @see prefuse.action.GroupAction#run(double)
	 */
	public void run(double frac) {
		TupleSet focus = m_vis.getGroup(Visualization.FOCUS_ITEMS);
		if (focus == null || focus.getTupleCount() == 0)
			return;

		Graph g = (Graph) m_vis.getGroup(m_group);
		Node f = null;
		Iterator<?> tuples = focus.tuples();
		while (tuples.hasNext() && !g.containsTuple(f = (Node) tuples.next())) {
			f = null;
		}
		if (f == null)
			return;
		g.getSpanningTree(f);
	}
}