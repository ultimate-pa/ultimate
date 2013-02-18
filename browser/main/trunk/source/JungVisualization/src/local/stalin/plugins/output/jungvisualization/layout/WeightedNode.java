package local.stalin.plugins.output.jungvisualization.layout;

import local.stalin.model.INode;

public class WeightedNode implements Comparable<WeightedNode>/*, Cloneable*/{
	
	private INode node;
	private float weight;
	private int layer;

	@Override
	public int compareTo(WeightedNode o) {
		 if (this.weight > o.weight){
			 return 1;
		 }
		 else if (this.weight < o.weight)
		 {
			 return -1;
		 }
		 else 
			 return 0;
	}

	public void setNode(INode node) {
		this.node = node;
	}

	public INode getNode() {
		return node;
	}

	public void setWeight(float weight) {
		this.weight = weight;
	}

	public float getWeight() {
		return weight;
	}

	public void setLayer(int layer) {
		this.layer = layer;
	}

	public int getLayer() {
		return layer;
	}
	
//	public Object clone() {
//		try {
//			return super.clone();
//		} 
//		catch (CloneNotSupportedException e) {
//			e.printStackTrace();
//			return null;
//		} 
//	}
}
