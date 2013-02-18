package local.stalin.plugins.output.jungvisualization.layout;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

import local.stalin.model.INode;


/*
 * computes xy coordinates using median function
 */
public class CoordinatesManager {

	private HashMap<String,INode> nodes;
	private HashMap<Integer, ArrayList<NodeInfo>> nodeOrder;
	private HashMap<String,NodeInfo> nodeInfos;

	public CoordinatesManager(HashMap<String,INode> nodes, HashMap<String,NodeInfo> nodeInfos , HashMap<Integer, ArrayList<NodeInfo>> nodeOrder){
		this.nodes = nodes;
		this.nodeOrder = nodeOrder;
		this.nodeInfos = nodeInfos;
	}
	


	private void setInitialX(){
		
		Iterator<Integer> iter = nodeOrder.keySet().iterator();
		float initX = 100;
		int nodeSep = 16;
		
		
		while (iter.hasNext()){
			
			int layer = iter.next().intValue();
			
			ArrayList<NodeInfo> currentLayer = nodeOrder.get(layer);
			
			//float minLayerWidth = currentLayer.size()*nodeSep; 
			
			float x = initX;
			
			for (NodeInfo ninfo : currentLayer){
				
				//minLayerWidth += ninfo.getWidth();
				ninfo.setXcoordinate(x);
				
				if (currentLayer.indexOf(ninfo) + 1 < currentLayer.size()){
					
					x += (ninfo.getWidth() + currentLayer.get(currentLayer.indexOf(ninfo) +1).getWidth())/2 + nodeSep;
				}
	
			}
			
			//System.out.println( layer + "   width    " + minLayerWidth);
			
		}
		
//		for (int layer = 1; nodeOrder.size() >= layer ; layer ++){
//
//			ArrayList<NodeInfo> currentLayer = nodeOrder.get(layer);
//			int x = 300;
//
//			for (int i = 0; currentLayer.size() > i; i++){//TODO
//				
//				NodeInfo currentNode = currentLayer.get(i);
//
//				if (i + 1 != currentLayer.size()){
//
//					NodeInfo nextNode = currentLayer.get(i+1);
//					currentNode.setXcoordinate(x);
//
//					x += (currentNode.getWidth() + nextNode.getWidth())/2 + 10;
//				}
//				
//				//System.out.println(nodes.get(currentNode.getStalinID()).getPayload().getName() + " at LAYER " + currentNode.getLayer() + " with X  " + currentNode.getXcoordinate());//TODO
//				//int y = initY + layer*layerDistance;
//				currentNode.setXcoordinate(x);
//				//setLocation(nodes.get(currentNode.getName()), x, y);
//			}
//
//		}
	}
	
	
	public void setY(){
		
		int layerSep = 60;//spaceHight/maxLevel;
		int initY = layerSep/2;
		float y = initY;
		Iterator<Integer> iter = nodeOrder.keySet().iterator();
		
		while (iter.hasNext()){

			Integer layer = iter.next();
			ArrayList<NodeInfo> currentLayerOrder = nodeOrder.get(layer);
			y = (layer -1)*layerSep + initY;
			for (NodeInfo ninfo : currentLayerOrder){

				ninfo.setYcoordinate(y);
				nodeInfos.put(ninfo.getStalinID(), ninfo);
				
			}
			
		}
		
	}
	
	

	public void setX(){
		setInitialX();
		//for (int i = 0; i<=2; i++){

		//	setMedianX();	
		//}
	}

	private void setMedianX(){

		for (int layer = 1; nodeOrder.size() > layer ; layer ++){

			ArrayList<NodeInfo> currentLayer = nodeOrder.get(layer);

			for (int i = 0; currentLayer.size() > i; i++){

				float x = getMedianX(currentLayer.get(i), layer + 1);

				currentLayer.get(i).setXcoordinate(x);
				System.out.println(x);
			}

		}

		for (int layer = nodeOrder.size()-1; layer > 1 ; layer--){

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
	private ArrayList<NodeInfo> getAdjacentNodes(NodeInfo nodeInfo, int adjacentLayer){
		ArrayList<NodeInfo> adjacentNodes = new ArrayList<NodeInfo>();

		List<INode> inodes = null;
		if (nodeInfo.getLayer() > adjacentLayer ){
			inodes = nodes.get(nodeInfo.getStalinID()).getOutgoingNodes();
		}
		else if (nodeInfo.getLayer() < adjacentLayer){
			inodes = nodes.get(nodeInfo.getStalinID()).getIncomingNodes();
		}

		if (inodes != null)
		{
			for (NodeInfo ninfo : nodeOrder.get(adjacentLayer)){

				for (INode i : inodes){

					if (ninfo.getStalinID().equals(i.getPayload().getID().toString())){

						adjacentNodes.add(ninfo);
					}	
				}
			}
		}

		return adjacentNodes;
	}
}
