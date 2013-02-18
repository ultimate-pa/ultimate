package local.stalin.plugins.output.jungvisualization.layout;

import java.awt.Font;
import java.awt.font.FontRenderContext;
import java.awt.geom.Rectangle2D;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

import local.stalin.model.IEdge;
import local.stalin.model.INode;
import local.stalin.plugins.output.jungvisualization.graph.GraphProperties;
import edu.uci.ics.jung.algorithms.importance.Ranking;
import edu.uci.ics.jung.algorithms.layout.AbstractLayout;
import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.visualization.VisualizationViewer;

public class TestLayout1 extends AbstractLayout<INode, IEdge> {

	private List<IEdge> backEdges;
	private INode rootNode;
	private HashMap<String,INode> nodes = new HashMap<String, INode>();
	//private ArrayList<NodeInfo> nodeInfoList = new ArrayList<NodeInfo>();
	private HashMap<String,NodeInfo> nodeInfos = new HashMap<String, NodeInfo>();
	private HashMap<Integer, ArrayList<NodeInfo>> nodeOrder = new HashMap<Integer, ArrayList<NodeInfo>>();
	
	//temporarily, ev. will be deleted
	private HashMap<INode,Integer> nodeLayers = new HashMap<INode,Integer>();
	private int maxLevel = 0;
	private HashMap<Integer, ArrayList<WeightedNode>> nodeOrderWithinLevels = new HashMap<Integer, ArrayList<WeightedNode>>();
	
	
	/* constructor */
	protected TestLayout1(Graph<INode, IEdge> graph) {
		super(graph);
		// TODO Auto-generated constructor stub
		setBackEdges(new ArrayList<IEdge>());
	}
	
	public TestLayout1(Graph<INode, IEdge> graph, List<IEdge> backEdges, INode rootNode){
		super(graph);
		setBackEdges(backEdges);
		setRootNode(rootNode);
	}
	
	

	@Override
	public void initialize() {
		// TODO Auto-generated method stub
		storeNodes();
		assignLayersToNodes(rootNode);
		storeLayerInfo();
		
		setXCoordinate();
		
	}

	@Override
	public void reset() {
		// TODO Auto-generated method stub
		
	}


	/* getter and setter methods */

	public void setBackEdges(List<IEdge> backEdges) {
		this.backEdges = backEdges;
	}



	public List<IEdge> getBackEdges() {
		return backEdges;
	}



	public void setRootNode(INode rootNode) {
		this.rootNode = rootNode;
	}



	public INode getRootNode() {
		return rootNode;
	}
	
	
	/* other methods */
	
	/**
	 * 
	 */
	private void setInitialXCoordinate(){
		
		//int layerDistance = 60;//spaceHight/maxLevel;
		//int initY = layerDistance/2;
		
		for (int layer = 0; nodeOrder.size() > layer ; layer ++){

			ArrayList<NodeInfo> currentLayer = nodeOrder.get(layer);

			for (int i = 0; currentLayer.size() > i; i++){
				int x = 300;
				NodeInfo currentNode = currentLayer.get(i);

				if (i + 1 != currentLayer.size()){

					NodeInfo nextNode = currentLayer.get(i+1);
					currentNode.setXcoordinate(x);

					x += (currentNode.getWidth() + nextNode.getWidth())/2 + 10;
				}

				//int y = initY + layer*layerDistance;
				currentNode.setXcoordinate(x);
				//setLocation(nodes.get(currentNode.getName()), x, y);
			}

		}
	}
	
	
	private void setXCoordinate(){
		setInitialXCoordinate();
		for (int i = 0; i<=2; i++){
			
			setMedianXCoordinate();	
		}
	}
	
	private void setMedianXCoordinate(){
		
		for (int layer = 0; nodeOrder.size() > layer ; layer ++){

			ArrayList<NodeInfo> currentLayer = nodeOrder.get(layer);

			for (int i = 0; currentLayer.size() > i; i++){
				
				float x = getMedianX(currentLayer.get(i), layer + 1);

				currentLayer.get(i).setXcoordinate(x);
			}

		}
		
		for (int layer = nodeOrder.size()-1; layer > 0 ; layer--){

			ArrayList<NodeInfo> currentLayer = nodeOrder.get(layer);

			for (int i = 0; currentLayer.size() > i; i++){
				
				float x = getMedianX(currentLayer.get(i), layer - 1);

				currentLayer.get(i).setXcoordinate(x);
			}

		}
		
	}
	
	/**
	 * 
	 * @param nodeInfo
	 * @param adjacentLayer
	 * @return  float: x-coordinate of an input node
	 */
	private float getMedianX(NodeInfo nodeInfo, int adjacentLayer){
		
		ArrayList<NodeInfo> adjacentNodes = getAdjacentNodes(nodeInfo, adjacentLayer);
		int numberOfAdjNodes = adjacentNodes.size();
		int m = numberOfAdjNodes/2; //index of the middle vertex
		
		if (numberOfAdjNodes == 0){
			return Float.NEGATIVE_INFINITY;
		}
		else if (numberOfAdjNodes%2 == 1){
			
			return adjacentNodes.get(m).getXcoordinate();
			
		}
		else {
			
			return (adjacentNodes.get(m-1).getXcoordinate() + adjacentNodes.get(m).getXcoordinate())/2;
		}
	}
	
	/**
	 * 
	 * @param nodeInfo
	 * @param adjacentLayer
	 * @return an ordered arraylist of node infos of incoming/outgoing nodes placed on the adjacent layer
	 */
	//returns  
	private ArrayList<NodeInfo> getAdjacentNodes(NodeInfo nodeInfo, int adjacentLayer){
		ArrayList<NodeInfo> adjacentNodes = new ArrayList<NodeInfo>();

		List<INode> inodes = null;
		if (nodeInfo.getLayer() > adjacentLayer ){
			inodes = nodes.get(nodeInfo.getStalinID()).getOutgoingNodes();
		}
		else if (nodeInfo.getLayer() < adjacentLayer){
			inodes = nodes.get(nodeInfo.getStalinID()).getIncomingNodes();
		}
		
		
		for (NodeInfo ninfo : nodeOrder.get(adjacentLayer)){
			
			for (INode i : inodes){
				
				if (ninfo.getStalinID().equals(i.getPayload().getID())){
					
					adjacentNodes.add(ninfo);
				}	
			}
		}
	
		return adjacentNodes;
	}
	
	
	//temporarily
	private void storeLayerInfo(){
		
		String id;
		NodeInfo ninfo = new NodeInfo();
		
		VisualizationViewer<INode, IEdge> vv = GraphProperties.getInstance().getVVforLayout();
		final Font font = vv.getFont();
		final FontRenderContext frc = vv.getFontMetrics(font).getFontRenderContext();
		
		Rectangle2D bounds;
		
		for (INode n : nodeLayers.keySet()){
			
			id = n.getPayload().getID().toString();
			bounds = font.getStringBounds(n.toString(), frc);
			
			ninfo.setWidth((float)bounds.getWidth() + 2);
			ninfo.setLayer(nodeLayers.get(n).intValue());
			ninfo.setStalinID(id);
			nodeInfos.put(id, ninfo);
		}
	}
	
	
	private void storeNodes(){
		
		List<INode> vertices = (List<INode>) getGraph().getVertices();
		
		for (INode n : vertices){
			
			nodes.put(n.getPayload().getID().toString(), n);
		}
	}
	
	//check whether useful
	//Ranking<INode> ranking = new Ranking<INode>(0, rankScore, ranked);
	
	
	//TODO: insert dummy nodes !!!
	//only! for directed acyclic graph 
	/**
	 * Assigns level to each vertex in the graph and stores them in a HashMap. 
	 * Traverses all the graph vertices with the help of BFS.
	 */
	private void assignLayersToNodes(INode root){
		int layer = 1;

		int oldLayer, newLayer;
		Queue<INode> nextQueue = new LinkedList<INode>();
		
		nextQueue.offer(root);
		this.nodeLayers.put(root, layer);
		
		while (nextQueue.isEmpty() == false)
		{
			INode node = nextQueue.remove();

			Collection<INode> children = getGraph().getSuccessors(node);

			if (children != null){
			
				layer = this.nodeLayers.get(node).intValue() + 1;
				maxLevel = layer;

				for (INode child: children){
					if(!this.nodeLayers.containsKey(child)){
						
						nextQueue.add(child);
						this.nodeLayers.put(child, new Integer(layer));
					}
					else{
						
						oldLayer = this.nodeLayers.get(child).intValue();
						if (oldLayer != layer)
						{
							this.nodeLayers.remove(child);
							newLayer = Math.max(oldLayer, layer);
							this.nodeLayers.put(child, new Integer(newLayer));
							nextQueue.add(child);

						}

					}
				}
				
			}
				
		}
		
	}
	

}
