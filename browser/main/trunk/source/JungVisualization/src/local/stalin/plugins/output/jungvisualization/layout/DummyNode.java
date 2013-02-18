package local.stalin.plugins.output.jungvisualization.layout;

import java.util.ArrayList;
import java.util.List;

import local.stalin.model.IEdge;
import local.stalin.model.INode;
import local.stalin.model.IPayload;
import local.stalin.model.Payload;

public class DummyNode implements INode {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	private List<INode> incomingNodes;
	private List<INode> outgoingNodes;
//	private List<IEdge> incomingEdges;
//	private List<IEdge> outgoingEdges;
	private Payload payload;
	

	public DummyNode(){
		incomingNodes = new ArrayList<INode>();
		outgoingNodes = new ArrayList<INode>();
//		incomingEdges = new ArrayList<IEdge>();
//		outgoingEdges = new ArrayList<IEdge>();
		payload = new Payload();
		payload.setName("d");
		setPayload(payload);
	}

	@Override
	public boolean addIncomingEdge(IEdge element) {
		// TODO Auto-generated method stub
		//this.incomingEdges.add(element);
		return false;
	}

	@Override
	public boolean addIncomingEdge(INode src) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean addIncomingNode(INode element) {
		// TODO Auto-generated method stub
		this.incomingNodes.add(element);
		return true;
	}

	@Override
	public boolean addOutgoingEdge(IEdge element) {
		// TODO Auto-generated method stub
		//this.outgoingEdges.add(element);
		return false;
	}

	@Override
	public boolean addOutgoingEdge(INode target) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean addOutgoingNode(INode element) {
		// TODO Auto-generated method stub
		this.outgoingNodes.add(element);
		return true;
	}

	@Override
	public int getChildCount() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public List<IEdge> getIncomingEdges() {
		// TODO Auto-generated method stub
		return  null;//this.incomingEdges;
	}

	@Override
	public List<INode> getIncomingNodes() {
		// TODO Auto-generated method stub
		return this.incomingNodes;
	}

	@Override
	public List<IEdge> getOutgoingEdges() {
		// TODO Auto-generated method stub
		return null;//this.outgoingEdges;
	}

	@Override
	public List<INode> getOutgoingNodes() {
		// TODO Auto-generated method stub
		return this.outgoingNodes;
	}

	@Override
	public void removeAllIncoming() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void removeAllOutgoing() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public boolean removeIncomingEdge(IEdge element) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean removeIncomingNode(INode element) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean removeOutgoingEdge(IEdge element) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean removeOutgoingNode(INode element) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public IPayload getPayload() {
		return payload;
	}

	@Override
	public boolean hasPayload() {
		return true;
	}

	@Override
	public void setPayload(IPayload payload) {
		// TODO Auto-generated method stub
		this.payload = (Payload)payload;
		
	}
	
	public String toString(){
	 return payload.getName();	
	}

}
