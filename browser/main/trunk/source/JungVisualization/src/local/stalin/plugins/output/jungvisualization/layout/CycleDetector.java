package local.stalin.plugins.output.jungvisualization.layout;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import local.stalin.model.IEdge;
import local.stalin.model.INode;
import edu.uci.ics.jung.graph.DirectedSparseMultigraph;
import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.graph.util.EdgeType;

//with the help of color DFS for directed graphs
public class CycleDetector {
	
	private Graph<INode, IEdge> graph;
	//private INode root;
	private ArrayList<IEdge> backEdges;
	
	private Map<INode, Integer> colors = new HashMap<INode, Integer>();
	public final static int WHITE = 0;
	public final static int GRAY = 1;
	public final static int BLACK = 2;
	
	
	
//	public CycleDetector(Graph<INode, IEdge> g, INode root){
//		setGraph(g);
//		setRoot(root);
//		backEdges = new ArrayList<IEdge>();
//	} 
	
	public CycleDetector(Graph<INode, IEdge> g){
		setGraph(g);
		backEdges = new ArrayList<IEdge>();
	} 
	

	public void removeCycles(INode root){
		
		for (INode n: graph.getVertices()){
			colors.put(n, WHITE);
		}
		
		if (getColor(root) == WHITE){

			visit(root);

		}
		
	}
	
	
	private void visit(INode node){

		if (colors.get(node) == WHITE){

			colors.put(node, GRAY);
			

			List<IEdge> outEdges = node.getOutgoingEdges();

			if (!outEdges.isEmpty()){

				for (IEdge edge : outEdges){
					
					if (getColor(edge.getTarget()) == GRAY){
				
						reverseEdge(edge);
						
						backEdges.add(edge);
					}
					else if(getColor(edge.getTarget()) == WHITE){

						visit(edge.getTarget());

					}
				}
			}
		}

		colors.put(node, BLACK);
		

	}
	
	
	private void reverseEdge(IEdge edge){
		
		graph.removeEdge(graph.findEdge(edge.getSource(), edge.getTarget()));
		
		INode source = edge.getSource();
		INode target = edge.getTarget();
		
		source.removeOutgoingNode(target);
		target.removeIncomingNode(source);
		
		source.addIncomingEdge(target);
		target.addOutgoingEdge(source);
		
		edge.setSource(target);
		edge.setTarget(source);
		
		graph.addEdge(edge, edge.getSource(), edge.getTarget(), EdgeType.DIRECTED);
	}
	
	

	public void setGraph(Graph<INode, IEdge> graph) {
		this.graph = graph;
	}

	public Graph<INode, IEdge> getGraph() {
		return graph;
	}

//	public void setBackEdges(ArrayList<IEdge> backEdges) {
//		this.backEdges = backEdges;
//	}

	public ArrayList<IEdge> getBackEdges() {
		return backEdges;
	}

	public void setColors(Map<INode, Integer> colors) {
		this.colors = colors;
	}

	public Map<INode, Integer> getColors() {
		return colors;
	}
	
	
	 public Integer getColor(INode n)
	    {
	        Integer color = colors.get(n);
	        return color != null ? color : WHITE;
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
