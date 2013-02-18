package local.stalin.plugins.output.jungvisualization.layout;

import local.stalin.model.IEdge;

public class WeightedEdge implements Comparable<WeightedEdge>/*, Cloneable*/{
	
	private IEdge edge;
	private float weight;

	@Override
	public int compareTo(WeightedEdge o) {
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

	public void setEdge(IEdge edge) {
		this.edge = edge;
	}

	public IEdge getEdge() {
		return edge;
	}

	public void setWeight(float weight) {
		this.weight = weight;
	}

	public float getWeight() {
		return weight;
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
