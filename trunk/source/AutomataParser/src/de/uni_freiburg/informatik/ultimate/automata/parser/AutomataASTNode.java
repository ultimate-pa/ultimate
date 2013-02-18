package de.uni_freiburg.informatik.ultimate.automata.parser;

import java.util.List;
import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.model.AbstractNoEdgeNode;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.Payload;

public class AutomataASTNode extends AbstractNoEdgeNode {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	private IPayload mPayload;
	private List<INode> children;
	private INode parent;
	
	public AutomataASTNode()
	{
		mPayload = new Payload();
		children = new ArrayList<INode>();
		parent = null;
	}
	
	public AutomataASTNode(IPayload payload)
	{
		mPayload = payload;
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
		return mPayload;
	}

	@Override
	public boolean hasPayload() {
		return mPayload != null;
	}

	@Override
	public void setPayload(IPayload payload) {
		this.mPayload = payload;
	}
	
	@Override
	public String toString()
	{
		assert this.mPayload!=null;
		assert this.mPayload.getAnnotations()!=null;
		assert this.mPayload.getAnnotations().get(Activator.PLUGIN_ID)!=null;
		return mPayload.getAnnotations().get(Activator.PLUGIN_ID).toString();
	}

}
