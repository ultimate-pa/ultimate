package local.stalin.plugins.output.jungvisualization.layout;

import java.util.ArrayList;
import java.util.HashMap;

import local.stalin.model.INode;

public class GraphCrossCounter1 {
	
	private HashMap<Integer, ArrayList<NodeInfo>> nodeOrder;
	HashMap<String, INode> nodes;

	
	public GraphCrossCounter1(HashMap<Integer, ArrayList<NodeInfo>> nodeOrder, HashMap<String, INode> nodes){
		setNodeOrder(nodeOrder);
		setNodes(nodes);
		
	}
	
	public GraphCrossCounter1(){
		setNodeOrder(null);
		setNodes(null);	
	}
	
	
	public int countCrossings(){
		
		int crossings = 0;
		
		if (nodeOrder != null && nodes != null){

			for (int layer = 0; nodeOrder.size() > layer ; layer ++){

				BilayerCrossCounter1 bcc = new BilayerCrossCounter1(nodeOrder.get(layer), nodeOrder.get(layer), nodes);
				crossings += bcc.countCrossings();
			}
		}
		
		return crossings;
	}

	
	public void setNodeOrder(HashMap<Integer, ArrayList<NodeInfo>> nodeOrder) {
		this.nodeOrder = nodeOrder;
	}

//	public HashMap<Integer, ArrayList<NodeInfo>> getNodeOrder() {
//		return nodeOrder;
//	}
	
	public void setNodes(HashMap<String,INode> nodes) {
		this.nodes = nodes;
	}

//	public HashMap<String,INode> getNodes() {
//		return nodes;
//	}
	
}
