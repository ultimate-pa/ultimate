package local.stalin.plugins.output.jungvisualization.layout;

public class NodeInfo implements Comparable<NodeInfo> {
	
	private String stalinID;
	private float weight = 0;
	private int layer = 0;
	private float xcoordinate = 0;
	private float ycoordinate = 0;
	private float width = 0;
	private boolean dummy = false;

	@Override
	public int compareTo(NodeInfo o) {
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

	public void setStalinID(String id) {
		this.stalinID = id;
	}

	public String getStalinID() {
		return stalinID;
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

	public void setXcoordinate(float xcoordinate) {
		this.xcoordinate = xcoordinate;
	}

	public float getXcoordinate() {
		return xcoordinate;
	}

	public void setDummy(boolean dummy) {
		this.dummy = dummy;
	}

	public boolean isDummy() {
		return dummy;
	}

	public void setWidth(float width) {
		this.width = width;
	}

	public float getWidth() {
		return width;
	}

	public void setYcoordinate(float ycoordinate) {
		this.ycoordinate = ycoordinate;
	}

	public float getYcoordinate() {
		return ycoordinate;
	}

}
