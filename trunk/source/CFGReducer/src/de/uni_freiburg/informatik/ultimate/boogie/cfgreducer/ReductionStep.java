package de.uni_freiburg.informatik.ultimate.boogie.cfgreducer;

import java.util.HashSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGExplicitNode;

public class ReductionStep {

	private HashSet<CFGExplicitNode>			m_visited			= new HashSet<CFGExplicitNode>();
	
	/*
	 * "source-predecessor" merges nodes that have only a single outgoing edge.
	 * Collects all edges that lead to a node that has more than one outgoing edge. These are merged later
	 * in order to reduce redundancy in edge assumptions.
	 */
	public boolean start(CFGExplicitNode source){
		boolean result = false;
		
		Logger.getLogger(Activator.PLUGIN_ID).debug("Reducing node " +
				source.getPayload().getName());
		boolean runCompression = false;
		CFGEdge edge = null;
		CFGExplicitNode target = null;

		//Check if source has already been visited and therefore already been reduced ...
		if (m_visited.contains(source)){
			//if source is already been reduced then return without taking any actions
			Logger.getLogger(Activator.PLUGIN_ID).debug("Node " +
					source.getPayload().getName() + "already visited.");
			return false;
		}
		m_visited.add(source);
		//Iterate through all edges of source node in order to start reducing
		for (IEdge iedge: source.getOutgoingEdges()){
			edge = (CFGEdge)iedge;
			target = (CFGExplicitNode)edge.getTarget();
			
			if (target == source){
				//source has a loop then ignore it
				continue;
			} else if (target.getIncomingEdges().size() > 1){
				/*target has more than one incoming edge; ignore this edge of source node
				 * also handles self-looping targets*/
				continue;
			} else if (target.getPayload().getName().contains("ERROR")) {
				/*target is an error node and must not be merged with predecessor. This can
				 * happen when reducing during safety checker loop.
				 */
				continue;
			} else {
				runCompression = true;
				break;
			}
		}
		if(runCompression){
			new SequentialCompression().run(edge);
			Logger.getLogger(Activator.PLUGIN_ID).debug("Reduction has been applied to " +
					source.getPayload().getName());
//			new ParallelCompression().run(source);
			return true;
		}
		
		/*iterates through all children of source if source has not done any reduction in order
		 * to reduce them*/
		for (IEdge iedge: source.getOutgoingEdges()){
			edge = (CFGEdge)iedge;
			//if a child of source has been reduced then break up and tell caller so
			result = result || this.start((CFGExplicitNode)edge.getTarget());
		}
//		if (result)
			result = result || (new ParallelCompression().run(source));
		//if no actions have taken place return false
		Logger.getLogger(Activator.PLUGIN_ID).debug("No reduction has been applied to " +
				source.getPayload().getName());
		return result;
	}
}
