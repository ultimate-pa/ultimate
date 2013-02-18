package local.stalin.plugins.output.jungvisualization.layout;

import java.awt.Font;
import java.awt.font.FontRenderContext;
import java.awt.geom.Rectangle2D;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

import local.stalin.model.IEdge;
import local.stalin.model.INode;
import local.stalin.plugins.output.jungvisualization.graph.GraphProperties;
import edu.uci.ics.jung.algorithms.layout.AbstractLayout;
import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.graph.event.GraphEvent.Vertex;
import edu.uci.ics.jung.graph.util.EdgeType;
import edu.uci.ics.jung.visualization.VisualizationViewer;

public class TestLayout extends /*Tree*/AbstractLayout<INode, IEdge> {
	
	private List<IEdge> backEdges;
	private INode rootNode;
	private HashMap<INode,Integer> nodeLevels = new HashMap<INode,Integer>();
	private HashMap<Integer, ArrayList<WeightedNode>> nodeOrderWithinLevels = new HashMap<Integer, ArrayList<WeightedNode>>();
	private NodeInfo nodeInfo = new NodeInfo();
	private int maxLevel = 0;
	static int graphHeight;


	protected TestLayout(Graph<INode, IEdge> graph) {
		super(graph);
		// TODO Auto-generated constructor stub
		setBackEdges(new ArrayList<IEdge>());
	}
	
	public TestLayout(Graph<INode, IEdge> graph, List<IEdge> backEdges, INode rootNode){
		super(graph);
		setBackEdges(backEdges);
		setRootNode(rootNode);
		//setGraph(graph);
		//System.out.println(" ******   Konstruktor   ******");
	}


	@Override
	public void initialize() {
		
		assignLevelToNodes(rootNode);
		initialNodeOrder();
//		ArrayList<WeightedNode> nNodes = nodeOrderWithinLevels.get(3);
//		ArrayList<WeightedNode> sNodes = nodeOrderWithinLevels.get(4);
//		BilayerCrossCounter bcc = new BilayerCrossCounter(nNodes, sNodes);
//		bcc.countCrossings();
		
		addBackEdges(backEdges);
		positionNodes();
	}

	@Override
	public void reset() {
		// TODO Auto-generated method stub
		
	}
	
	public void setBackEdges(List<IEdge> backEdges){
		this.backEdges = backEdges;
	}
	
	public void setRootNode(INode root){
		this.rootNode = root;
	}
	
//	public void setGraph(Graph<INode, IEdge> g){
//		this.graph = g;
//	}
	
	public void addBackEdges(List<IEdge> backEdges){
		//System.out.println("Adding back edges:");
		if (!backEdges.isEmpty()){
			for (IEdge backedge : backEdges){
				
				//System.out.println( backedge.getSource() + " ----->"  +  backedge.getTarget());
				getGraph().addEdge(backedge, backedge.getSource(), backedge.getTarget(), EdgeType.DIRECTED);
			}
		}
		
	}
	
	//only! for directed acyclic graph 
	/**
	 * Assigns level to each vertex in the graph and stores them in a HashMap. 
	 * Traverses all the graph vertices with the help of BFS.
	 */
	public void assignLevelToNodes(INode root){
		int level = 0;
		//int rank = 0;
		int oldLevel, newLevel;
		Queue<INode> nextQueue = new LinkedList<INode>();
		//List<INode> children = node.getIncomingNodes();
		//System.out.println(" ***** assigning levels to nodes *****");
		
		nextQueue.offer(root);
		this.nodeLevels.put(root, level);
		//this.nodeRanksWithinLevels.put(root, rank);
		
		while (nextQueue.isEmpty() == false)
		{
			INode node = nextQueue.remove();

			Collection<INode> children = getGraph().getSuccessors(node);

			if (children != null){
				
				//level = level + 1;
				/* Korrektur 1: level von parent nehmen*/
				level = this.nodeLevels.get(node).intValue() + 1;
				maxLevel = level;
			//	rank = 1;
				
				
				//System.out.println("**** max level is " + maxLevel + " *******");

				for (INode child: children){
				//	this.nodeRanksWithinLevels.put(child, rank);
					//if (rank > maxRankWithinLevel){
					//	maxRankWithinLevel = rank;
					//}
					//check if child node already has its level assignment
					if(!this.nodeLevels.containsKey(child)){
						
						nextQueue.add(child);
						this.nodeLevels.put(child, new Integer(level));
					}
					else{
						
						oldLevel = this.nodeLevels.get(child).intValue();
						if (oldLevel != level)
						{
							this.nodeLevels.remove(child);
							newLevel = Math.max(oldLevel, level);
							this.nodeLevels.put(child, new Integer(newLevel));
							nextQueue.add(child);
							//System.out.println(child.toString());
						}

					}
					//System.out.println("Level of nodes = "+ this.nodeLevels.values());
					//rank = rank +1;
				}//end of for
				
			}
			//System.out.println(nodeLevels.toString());	
		}
		
	}
	
	
	//initial node ordering
	private void initialNodeOrder(){
		
		Iterator<INode> it = nodeLevels.keySet().iterator();
		
		while (it.hasNext()){
			INode node = (INode)it.next();
			int i = nodeLevels.get(node);
			if(!nodeOrderWithinLevels.containsKey(i)){
				ArrayList<WeightedNode> order = new ArrayList<WeightedNode>();
				for (INode n : nodeLevels.keySet()){
					if (nodeLevels.get(n).intValue() == i){
						WeightedNode wNode = new WeightedNode();
						wNode.setNode(n);
						wNode.setWeight(-3);
						order.add(wNode);
					}
				}
				nodeOrderWithinLevels.put(i, order);
			}

		}
		//System.out.println(nodeOrderWithinLevels);

	}
	
	//TODO: rename
	private ArrayList<Integer> getAdjacentPositions(INode node, int level){
		ArrayList<Integer> adjacentPositions = new ArrayList<Integer>();
		List<INode> incomingNodes = node.getIncomingNodes();
		ArrayList<WeightedNode> adjacentNodes = nodeOrderWithinLevels.get(level);
		for (INode n: incomingNodes){
			
			int adjPosition = adjacentNodes.indexOf(n)+1;
			adjacentPositions.add(adjPosition);
		}
		
		return adjacentPositions;
	}
	
	//returns an ordered arraylist of incoming/outgoing weighted nodes placed on the adjacent layer 
	private ArrayList<WeightedNode> getAdjacentNodes(WeightedNode wnode, int adjacentLayer){
		ArrayList<WeightedNode> adjacentNodes = new ArrayList<WeightedNode>();

		List<INode> inodes = null;
		if (wnode.getLayer() > adjacentLayer ){
			inodes = wnode.getNode().getOutgoingNodes();
		}
		else if (wnode.getLayer() < adjacentLayer){
			inodes = wnode.getNode().getIncomingNodes();
		}
		
		
		for (WeightedNode w : nodeOrderWithinLevels.get(adjacentLayer)){
			
			for (INode i : inodes){
				
				if (w.getNode().equals(i)){
					
					adjacentNodes.add(w);
				}
					
				
			}
		}
		
		
		return adjacentNodes;
	}
	
	
	/**
	 * Implementation of median_value(v,adj_rank) procedure taken from the paper
	 * "A Technique for Drawing Directed Graphs", IEEE Transactions on Software Engineering, Vol. 19, 1993
	 * by E. Gansner, E. Kousofios, S. North, K-P. Vo
	 */
	private float getMedianValue(INode node, int adjacentLayer){
		float medianValue = 0;
		ArrayList<Integer> adjacentPositions = this.getAdjacentPositions(node, adjacentLayer);
		//System.out.println(adjacentPositions);
		int numberAdjPositions = adjacentPositions.size();
		
		int m = adjacentPositions.size()/2;
		
		if (numberAdjPositions == 0){
			medianValue = -1;
		}
		else if (numberAdjPositions%2 == 1){
			medianValue = adjacentPositions.get(m);//ordering number of middle node
		}
		else if (numberAdjPositions == 2){
			medianValue = (adjacentPositions.get(0) + adjacentPositions.get(1))/2;
		}
		else{
			int left =  adjacentPositions.get(m-1)- adjacentPositions.get(0);
			int right = adjacentPositions.get(numberAdjPositions-1)-adjacentPositions.get(m);
			medianValue = (adjacentPositions.get(m-1)*right + adjacentPositions.get(m)*left)/(left+right);
		}
		
		return medianValue;
	}
	
	/**
	 * Implementation of wmedian(order,iter) procedure taken from the paper
	 * "A Technique for Drawing Directed Graphs", IEEE Transactions on Software Engineering, Vol. 19, 1993
	 * by E. Gansner, E. Kousofios, S. North, K-P. Vo
	 */
	private void weightedNodeOrder(HashMap<Integer, ArrayList<WeightedNode>> order, int iter){
		
		if (iter%2 == 0){

			for (int level = 0; level <= maxLevel; level ++){
				for (WeightedNode wnode : nodeOrderWithinLevels.get(level)){
					wnode.setWeight(getMedianValue(wnode.getNode(), level-1));
				}
				Collections.sort(nodeOrderWithinLevels.get(level));
			}
		}
		
	}
	
	private void finalNodeOrder(){
		
	}
	
	
	private void positionNodes(){
		int layerDistance = 60;//spaceHight/maxLevel;
		int initY = layerDistance/2;
		//System.out.println("HEIGHT = " + spaceHight + " WIDTH = " + spaceWidth);
		
		
		for (int layer = 0; nodeOrderWithinLevels.size() > layer ; layer ++){
			
			ArrayList<WeightedNode> currentLayer = nodeOrderWithinLevels.get(layer);
			//Iterator<WeightedNode> iter = nodeOrderWithinLevels.get(level).iterator();
			
			for (int i = 0; currentLayer.size() > i; i++){
				int x = 300;
				WeightedNode currentWNode = currentLayer.get(i);
				
				if (i + 1 != currentLayer.size()){
				
				WeightedNode nextWNode = currentLayer.get(i+1);
				
				x += getMinDistance(currentWNode.getNode(), nextWNode.getNode());
				}
				
				int y = initY + nodeLevels.get(currentWNode.getNode()).intValue()*layerDistance;
				setLocation(currentWNode.getNode(), x, y);
			}
				
		}
	}
	
	//xsize of node
	private double getXSize(INode n){
		VisualizationViewer<INode, IEdge> vv = GraphProperties.getInstance().getVVforLayout();
		final Font font = vv.getFont();
		final FontRenderContext frc = vv.getFontMetrics(font).getFontRenderContext();
		
		
		
		Rectangle2D bounds = font.getStringBounds(n.toString(), frc);
		double xSize = bounds.getWidth()+2;
	
		return xSize;
	}
	
	//min distance between nodes' center points, depending on nodes' size
	private double getMinDistance(INode n1, INode n2){
		double minDistance  = (getXSize(n1) + getXSize(n2))/2 + 10;
		return minDistance;
	}
	
//	private double computeInitialX(INode n1, INode n2){
//		double initX = 300 + getMinDistance(n1, n2);
//		
//		return initX;
//	}
	
	//Nachfolger betrachten
	private float getMedianX(WeightedNode wnode, int adjacentLayer){
		float medianX = 0;
		ArrayList<Integer> adjacentPositions = this.getAdjacentPositions(wnode.getNode(), adjacentLayer);
		ArrayList<WeightedNode> adjacentNodes = this.getAdjacentNodes(wnode, adjacentLayer);
		//System.out.println(adjacentPositions);
		int numberAdjNodes = adjacentNodes.size();
		
		int m = adjacentNodes.size()/2;
		
		if (numberAdjNodes == 0){
			medianX = Float.NEGATIVE_INFINITY;
		}
		else if (numberAdjNodes%2 == 1){
			//medianX = adjacentNodes.get(m).getNode();//ordering number of middle node
			Vertex<INode, IEdge> n;
			
		}
//		else if (numberAdjNodes == 2){
//			medianX = (adjacentPositions.get(0) + adjacentPositions.get(1))/2;
//		}
		else{
			int left =  adjacentPositions.get(m-1)- adjacentPositions.get(0);
			int right = adjacentPositions.get(numberAdjNodes-1)-adjacentPositions.get(m);
			medianX = (adjacentPositions.get(m-1)*right + adjacentPositions.get(m)*left)/(left+right);
		}
		
		return medianX;
	}
	
	
	
	
		
}
