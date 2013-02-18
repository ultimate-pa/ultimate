package local.stalin.plugins.output.jungvisualization.layout;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

import local.stalin.model.IEdge;
import local.stalin.model.INode;

/**
 * Implementation of cross counting approach by W. Barth, P. Mutzel and M. Jünger
 * @author lena
 *
 */
public class BilayerCrossCounter1 {
	
	private ArrayList<NodeInfo> northNodes;
	private ArrayList<NodeInfo> southNodes;
	private ArrayList<Integer> edgesOrder;
	private HashMap<String,INode> nodes;
	private int[] heap;
	
	
	
	public BilayerCrossCounter1(ArrayList<NodeInfo> northNodes, ArrayList<NodeInfo> southNodes, HashMap<String,INode> nodes){
		setNorthNodes(northNodes);
		setSouthNodes(southNodes);
		setNodes(nodes);
	}
	
	/**
	 * 
	 * @param northNodes
	 * @param southNodes
	 */
	public BilayerCrossCounter1(ArrayList<NodeInfo> northNodes, ArrayList<NodeInfo> southNodes){
		setNorthNodes(northNodes);
		setSouthNodes(southNodes);
		setNodes(null);
	}
	
	/**
	 * 
	 */
	public BilayerCrossCounter1(){
		setNorthNodes(null);
		setSouthNodes(null);
	}

	/**
	 * 
	 * @param northNodes
	 */
	public void setNorthNodes(ArrayList<NodeInfo> northNodes){
		this.northNodes = northNodes;
	}
	
	/**
	 * 
	 * @param southNodes
	 */
	public void setSouthNodes(ArrayList<NodeInfo> southNodes){
		this.southNodes = southNodes;
	}
	
	/**
	 * 
	 * @return
	 */
	public int countCrossings(){
		int crossings = 0;
		
		if (northNodes != null && southNodes != null){
			initDataStructures();
			
			Iterator<Integer> edgeOrderIt = edgesOrder.iterator();
			while (edgeOrderIt.hasNext()) {
				int currentNodeIndex = edgeOrderIt.next().intValue();
				int currentHeapIndex = getNodesHeapIndex(currentNodeIndex);
				
				do {
					heap[currentHeapIndex] ++;
					
					int rightIndex = getRightSiblingIndex(currentHeapIndex);
					if (rightIndex > 0) {
						crossings += heap[rightIndex];
					}
					
					currentHeapIndex = getParentIndex(currentHeapIndex);
				} while (currentHeapIndex >= 0);
			}
		}
		
		//System.out.println("CROSSINGS = " + crossings);
		
		return crossings;
	}
	
	/**
	 * 
	 */
	private void initDataStructures(){
		// init heap
		int q = southNodes.size();
		int c = 1;
		while (c < q){
			c = c*2;
		}
		int heapSize = 2*c - 1;
		heap = new int[heapSize];
		for (int t = 0; t<heapSize; t++) heap[t] = 0;
		
		// init edge order
		edgesOrder = new ArrayList<Integer>();
		Iterator<NodeInfo> nodeIt = northNodes.iterator();
		Iterator<IEdge> edgeIt;
		Iterator<WeightedEdge> wEdgeIt;
		NodeInfo currentNode;
		WeightedEdge currentWEdge;
		
		while (nodeIt.hasNext()){
			currentNode = nodeIt.next();
			
			List<IEdge> edgeList = nodes.get(currentNode.getStalinID()).getOutgoingEdges();
			ArrayList<WeightedEdge> weightedEdges = new ArrayList<WeightedEdge>();
			
			edgeIt = edgeList.iterator();
			while (edgeIt.hasNext()) {
				currentWEdge = new WeightedEdge();
				currentWEdge.setEdge(edgeIt.next());
				setEdgeWeight (currentWEdge);
				weightedEdges.add(currentWEdge);
			}
			Collections.sort(weightedEdges);
			
			wEdgeIt = weightedEdges.iterator();
			while (wEdgeIt.hasNext()) {
				currentWEdge = wEdgeIt.next();
				
				// Kantengewicht ist Position des Suedknotens
				edgesOrder.add(new Integer ((int) currentWEdge.getWeight()));
			}
		}
	}
	
	// TODO: das muss noch effizienter werden
	/**
	 * 
	 */
	private void setEdgeWeight(WeightedEdge wEdge) {
		int weight = Integer.MAX_VALUE;
		
		Iterator<NodeInfo> nodeIt = southNodes.iterator();
		NodeInfo currentNode;
		
		int i = 0;
		
		while (nodeIt.hasNext()) {
			currentNode = nodeIt.next();
			if (nodes.get(currentNode.getStalinID()).equals(wEdge.getEdge().getTarget())) {
				weight = i;
				break;
			}
			i++;
		}
		
		wEdge.setWeight(weight);
	}
	
	/**
	 * 
	 * @param heapIndex
	 * @return
	 */
	private boolean isLeftChild (int heapIndex){
		return heapIndex % 2 == 1;
	}
	
	/**
	 * 
	 * @param heapIndex
	 * @return
	 */
	private int getRightSiblingIndex (int heapIndex){
		if (isLeftChild(heapIndex)) {
			return heapIndex + 1;
		} else {
			return -1;
		}
	}
	
	/**
	 * 
	 * @param heapIndex
	 * @return
	 */
	private int getParentIndex (int heapIndex){
		if (heapIndex > 0) {
			return (heapIndex - 1) / 2;
		} else {
			return -1;
		}
	}
	
	/**
	 * 
	 * @param nodeIndex
	 * @return
	 */
	private int getNodesHeapIndex (int nodeIndex){
		int firstNodeHeapIndex = heap.length / 2;
		return firstNodeHeapIndex + nodeIndex;
	}

	public void setNodes(HashMap<String,INode> nodes) {
		this.nodes = nodes;
	}

	public HashMap<String,INode> getNodes() {
		return nodes;
	}
}
