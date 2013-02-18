/*
 * Project:	CoreRCP
 * Package:	de.uni_freiburg.informatik.ultimate.model
 * File:	DefaultNoEdgeNode.java created on Nov 26, 2009 by Björn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.model;

import java.util.ArrayList;
import java.util.List;

/**
 * DefaultNoEdgeNode
 *
 * @author Björn Buchhold
 *
 */
public class DefaultNoEdgeNode extends AbstractNoEdgeNode {

	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = -8289673298976654612L;
	private List<INode> incoming = new ArrayList<INode>();
	private List<INode> outgoing = new ArrayList<INode>();
	
	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.model.INode#addIncomingNode(de.uni_freiburg.informatik.ultimate.model.INode)
	 */
	@Override
	public boolean addIncomingNode(INode element) {
		return this.incoming.add(element);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.model.INode#addOutgoingNode(de.uni_freiburg.informatik.ultimate.model.INode)
	 */
	@Override
	public boolean addOutgoingNode(INode element) {
		return this.outgoing.add(element);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.model.INode#getIncomingNodes()
	 */
	@Override
	public List<INode> getIncomingNodes() {
		return this.incoming;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.model.INode#getOutgoingNodes()
	 */
	@Override
	public List<INode> getOutgoingNodes() {
		return this.outgoing;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.model.INode#removeAllIncoming()
	 */
	@Override
	public void removeAllIncoming() {
		this.incoming.clear();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.model.INode#removeAllOutgoing()
	 */
	@Override
	public void removeAllOutgoing() {
		this.outgoing.clear();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.model.INode#removeIncomingNode(de.uni_freiburg.informatik.ultimate.model.INode)
	 */
	@Override
	public boolean removeIncomingNode(INode element) {
		return this.incoming.remove(element);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.model.INode#removeOutgoingNode(de.uni_freiburg.informatik.ultimate.model.INode)
	 */
	@Override
	public boolean removeOutgoingNode(INode element) {
		return this.outgoing.remove(element);
	}

}
