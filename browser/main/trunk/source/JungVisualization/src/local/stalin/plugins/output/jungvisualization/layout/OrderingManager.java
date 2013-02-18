package local.stalin.plugins.output.jungvisualization.layout;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

import local.stalin.model.INode;



public class OrderingManager {
	
	private HashMap<String,INode> nodes = new HashMap<String, INode>();
	private HashMap<String,NodeInfo> nodeInfos = new HashMap<String, NodeInfo>();
	private HashMap<INode,Integer> nodeLayers = new HashMap<INode,Integer>();
	private HashMap<Integer, ArrayList<NodeInfo>> nodeOrder = new HashMap<Integer, ArrayList<NodeInfo>>();
	
	public OrderingManager(HashMap<String,INode> nodes,HashMap<String,NodeInfo> nodeInfos, HashMap<INode,Integer> nodeLayers){
		this.nodes = nodes;
		this.nodeInfos = nodeInfos;
		this.nodeLayers = nodeLayers;
	}
	
	
	public HashMap<Integer, ArrayList<NodeInfo>> getNodeOrder(){

		initialNodeOrder();
		//fehlt weighted node order
		
		//testing();
		return nodeOrder;
	}
	
	
	//TODO:remove! only for testing!!!
	private void testing(){
		
		Iterator<INode> it = nodeLayers.keySet().iterator();
		
		while (it.hasNext()){
			INode in = it.next();
			System.out.println("Layers :::::" + in + " at "  +  nodeLayers.get(in));
		}
		
		Iterator<Integer> iter = nodeOrder.keySet().iterator();
		
		while (iter.hasNext()){
			Integer layer = iter.next();
			
			for (NodeInfo ni : nodeOrder.get(layer)){
				
				System.out.println(nodes.get(ni.getStalinID()) + "   at layer  " + layer);
				
			}
		}
			
		
	}
	
	
	//initial node ordering
	private void initialNodeOrder(){
		
		Iterator<INode> it = nodeLayers.keySet().iterator();
		
		while (it.hasNext()){
			
			INode node = (INode)it.next();
			int layer = nodeLayers.get(node);
			ArrayList<NodeInfo> order = new ArrayList<NodeInfo>();
			
			if(!nodeOrder.containsKey(layer)){

				order.add(nodeInfos.get(node.getPayload().getID().toString()));
				nodeOrder.put(layer, order);
			}
			else{
				order = nodeOrder.get(layer);
				order.add(nodeInfos.get(node.getPayload().getID().toString()));
			}
			
			nodeOrder.put(layer, order);

		}

	}
	
	//TODO: rename
	private ArrayList<Integer> getAdjacentPositions(INode node, int level){
		ArrayList<Integer> adjacentPositions = new ArrayList<Integer>();
		List<INode> incomingNodes = node.getIncomingNodes();
		ArrayList<NodeInfo> adjacentNodes = nodeOrder.get(level);
		for (INode n: incomingNodes){
			
			int adjPosition = adjacentNodes.indexOf(n)+1;
			adjacentPositions.add(adjPosition);
		}
		
		return adjacentPositions;
	}
	
	//returns an ordered arraylist of incoming/outgoing weighted nodes placed on the adjacent layer 
	private ArrayList<NodeInfo> getAdjacentNodes(NodeInfo nodeInfo, int adjacentLayer){
		ArrayList<NodeInfo> adjacentNodes = new ArrayList<NodeInfo>();

		List<INode> inodes = null;
		if (nodeInfo.getLayer() > adjacentLayer ){
			inodes =  nodes.get(nodeInfo.getStalinID()).getOutgoingNodes();  //nodeInfo.getNode().getOutgoingNodes();
		}
		else if (nodeInfo.getLayer() < adjacentLayer){
			inodes = nodes.get(nodeInfo.getStalinID()).getIncomingNodes();
		}
		
		
		for (NodeInfo ninfo : nodeOrder.get(adjacentLayer)){
			
			for (INode i : inodes){
				
				if (nodes.get(nodeInfo.getStalinID()).equals(i)){
					
					adjacentNodes.add(ninfo);
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

			for (int layer = 0; layer <= nodeOrder.size()+1; layer ++){
				for (NodeInfo ninfo : nodeOrder.get(layer)){
					ninfo.setWeight(getMedianValue(nodes.get(ninfo.getStalinID()), layer-1));
				}
				Collections.sort(nodeOrder.get(layer));
			}
		}
		
	}

}
