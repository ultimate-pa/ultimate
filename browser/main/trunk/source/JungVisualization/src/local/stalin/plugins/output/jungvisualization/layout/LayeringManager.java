package local.stalin.plugins.output.jungvisualization.layout;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Queue;

import local.stalin.model.IEdge;
import local.stalin.model.INode;
import edu.uci.ics.jung.graph.Graph;



public class LayeringManager {
	
	private HashMap<INode,Integer> nodeLayers = new HashMap<INode,Integer>();
	//private Graph<INode, IEdge> graph;
	//private INode root;

	
//	public LayeringManager(Graph<INode, IEdge> graph, INode root){
//		this.graph = graph;
//		setRoot(root);
//	}
	
	public LayeringManager(){
	}
	
	//TODO: insert dummy nodes !!!
	//only! for directed ACYCLIC graph 
	/**
	 * Assigns level to each vertex in the graph and stores them in a HashMap. 
	 * Traverses all the graph vertices with the help of BFS.
	 */
	public HashMap<INode,Integer> getLayers(Graph<INode, IEdge> graph, INode root){
		int layer = 1;

		int oldLayer; //newLayer;
		Queue<INode> nextQueue = new LinkedList<INode>();
		
		nextQueue.offer(root);
		this.nodeLayers.put(root, layer);
		
		while (nextQueue.isEmpty() == false)
		{
			INode node = nextQueue.remove();

			Collection<INode> children = graph.getSuccessors(node);

			if (children != null){
			
				layer = this.nodeLayers.get(node).intValue() + 1;

				for (INode child: children){
					if(!this.nodeLayers.containsKey(child)){
						
						nextQueue.add(child);
						this.nodeLayers.put(child, new Integer(layer));
					}
					else{
						
						oldLayer = this.nodeLayers.get(child).intValue();
						if (oldLayer != layer)
						{
							this.nodeLayers.put(child, new Integer(layer));
							nextQueue.add(child);
						}

					}
				}
				
			}
				
		}
		
		
		return nodeLayers;
	}
	

	

//	public void setRoot(INode root) {
//		this.root = root;
//	}
//
//
//	public INode getRoot() {
//		return root;
//	}

}
