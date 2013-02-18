package local.stalin.automata.parser;

import java.util.List;
import java.util.ArrayList;

import local.stalin.model.AbstractNoEdgeNode;
import local.stalin.model.IEdge;
import local.stalin.model.INode;
import local.stalin.model.IPayload;
import local.stalin.model.Payload;

public class AutomataASTNode extends AbstractNoEdgeNode {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	private IPayload payload;
	private List<INode> children;
	private INode parent;
	
	public AutomataASTNode()
	{
		payload = new Payload();
		children = new ArrayList<INode>();
		parent = null;
	}
	
	@Override
	public boolean addIncomingNode(INode element) {
		parent = element;
		return true;
	}

	@Override
	public boolean addOutgoingNode(INode element) {
		children.add(element);
		element.addIncomingNode(this);
		return true;
	}

	@Override
	public List<INode> getIncomingNodes() {
		ArrayList<INode> temp = new ArrayList<INode>();
		temp.add(parent);
		return temp;
	}

	@Override
	public List<INode> getOutgoingNodes() {
		return children;
	}

	@Override
	public void removeAllIncoming() {
		parent = null;
	}

	@Override
	public void removeAllOutgoing() {
		children = new ArrayList<INode>();

	}

	@Override
	public boolean removeIncomingNode(INode element) {
		if(element.equals(parent))
		{
			parent = null;
			return true;
		}
		return false;
	}

	@Override
	public boolean removeOutgoingNode(INode element) {
		if(children.contains(element))
		{
			children.remove(element);
			return true;
		}
		return false;
	}

	@Override
	public IPayload getPayload() {
		return payload;
	}

	@Override
	public boolean hasPayload() {
		return payload != null;
	}

	@Override
	public void setPayload(IPayload payload) {
		this.payload = payload;
	}
	
	@Override
	public String toString()
	{
		assert this.payload!=null;
		assert this.payload.getAnnotations()!=null;
		assert this.payload.getAnnotations().get(Activator.PLUGIN_ID)!=null;
		return payload.getAnnotations().get(Activator.PLUGIN_ID).toString();
	}

}
