package local.stalin.model.boogie.ast.wrapper;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import local.stalin.model.AbstractNoEdgeNode;
import local.stalin.model.Flags;
import local.stalin.model.INode;
import local.stalin.model.IPayload;
import local.stalin.model.Payload;

public class WrapperNode extends AbstractNoEdgeNode {
	private static final long serialVersionUID = 203486790200450017L;
	
	private WrapperNode parent;
	private List<INode> children;
	private Object backing;
	private Payload payload;
	
	public WrapperNode(WrapperNode parent, Object backing) {
		this.parent = parent;
		this.backing = backing;
	}

	//@Override
	public boolean addIncomingNode(INode element) {
		throw new UnsupportedOperationException();
	}

	//@Override
	public boolean addOutgoingNode(INode element) {
		throw new UnsupportedOperationException();
	}

	//@Override
	public List<INode> getIncomingNodes() {
		if (parent != null)
			return Collections.singletonList((INode) parent);
		return Collections.emptyList();
	}

	//@Override
	public List<INode> getOutgoingNodes() {
		if (children != null)
			return children;
			
		children = new LinkedList<INode>();
		if (backing instanceof ASTNode) {
			for (Object c : ((ASTNode) backing).getChildren()) {
				children.add(new WrapperNode(this, c));
			}
		} else if (backing instanceof Object[]) {
			for (Object c : (Object[]) backing) {
				children.add(new WrapperNode(this, c));
			}
		} else {
			children = Collections.emptyList();
		}
		return children;
	}

	//@Override
	public void removeAllIncoming() {
		throw new UnsupportedOperationException();
	}

	//@Override
	public void removeAllOutgoing() {
		throw new UnsupportedOperationException();
	}

	//@Override
	public boolean removeIncomingNode(INode element) {
		throw new UnsupportedOperationException();
	}

	//@Override
	public boolean removeOutgoingNode(INode element) {
		throw new UnsupportedOperationException();
	}

	//@Override
	public void setDepth(int depth) {
		/* ignore */
	}

	//@Override
	public Flags getFlags() {
		return null;
	}

	//@Override
	public IPayload getPayload() {
		if (backing instanceof ASTNode) {
			return ((ASTNode) backing).getPayload();
		}
		if (payload != null)
			return payload;
		if (backing instanceof Object[]) {
			payload = new Payload(null, 
					backing.getClass().getComponentType().getName().toUpperCase() + "_LIST");
//			payload.setChildCount(((Object[]) backing).length);
		} else if (backing == null) {
			payload = new Payload(null, "NULL");
		} else {
			payload = new Payload(null, backing.toString());
		}
		return payload;
	}

	//@Override
	public boolean hasPayload() {
		return backing != null;
	}

	//@Override
	public void setPayload(IPayload payload) {
		throw new UnsupportedOperationException();
	}

	public Object getBacking() {
		return backing;
	}
}
