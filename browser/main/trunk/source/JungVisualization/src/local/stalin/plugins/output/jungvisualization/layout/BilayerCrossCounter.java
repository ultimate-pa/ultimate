package local.stalin.plugins.output.jungvisualization.layout;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

import local.stalin.model.IEdge;

public class BilayerCrossCounter {
	
	private ArrayList<WeightedNode> northNodes;
	private ArrayList<WeightedNode> southNodes;
	private ArrayList<Integer> edgesOrder;
	private int[] heap;
	
	/**
	 * 
	 * @param northNodes
	 * @param southNodes
	 */
	public BilayerCrossCounter(ArrayList<WeightedNode> northNodes, ArrayList<WeightedNode> southNodes){
		setNorthNodes(northNodes);
		setSouthNodes(southNodes);
	}
	
	/**
	 * 
	 */
	public BilayerCrossCounter(){
		setNorthNodes(null);
		setSouthNodes(null);
	}

	/**
	 * 
	 * @param northNodes
	 */
	public void setNorthNodes(ArrayList<WeightedNode> northNodes){
		this.northNodes = northNodes;
	}
	
	/**
	 * 
	 * @param southNodes
	 */
	public void setSouthNodes(ArrayList<WeightedNode> southNodes){
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
		Iterator<WeightedNode> nodeIt = northNodes.iterator();
		Iterator<IEdge> edgeIt;
		Iterator<WeightedEdge> wEdgeIt;
		WeightedNode currentWNode;
		WeightedEdge currentWEdge;
		
		while (nodeIt.hasNext()){
			currentWNode = nodeIt.next();
			
			List<IEdge> edgeList = currentWNode.getNode().getOutgoingEdges();
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
		
		Iterator<WeightedNode> nodeIt = southNodes.iterator();
		WeightedNode currentWNode;
		
		int i = 0;
		
		while (nodeIt.hasNext()) {
			currentWNode = nodeIt.next();
			if (currentWNode.getNode().equals(wEdge.getEdge().getTarget())) {
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
}
