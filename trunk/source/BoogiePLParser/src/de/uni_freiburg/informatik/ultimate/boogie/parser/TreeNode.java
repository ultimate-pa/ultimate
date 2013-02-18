package de.uni_freiburg.informatik.ultimate.boogie.parser;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.AbstractNoEdgeNode;
import de.uni_freiburg.informatik.ultimate.model.AbstractUnlabeledEdgeNodeTreeFactory;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.IPayload;

/**
 * 
 * This is an INode used with AntLR. It holds an instance of an INode which
 * implementation can change later.
 * 
 * @author Bisser
 * @since 425
 * 
 *        $LastChangedBy: ermis $ <br>
 *        $LastChangedRevision: 601 $ <br>
 *        $LastChangedDate: 2008-06-10 16:17:34 +0200 (Di, 10 Jun 2008) $ <br>
 */
public class TreeNode extends AbstractNoEdgeNode {

	private INode m_Node;
	private static transient AbstractUnlabeledEdgeNodeTreeFactory s_Factory = AbstractUnlabeledEdgeNodeTreeFactory
			.getFactory();
	protected int m_startIndex = -1;
	protected int m_stopIndex = -1;
	private static final long serialVersionUID = 1189715172369009711L;

	/**
	 * Basic constructor
	 */
	public TreeNode() {
		m_Node = s_Factory.createNode();
	}

	/**
	 * Constructor with a Ultimate payload
	 * 
	 * @param payload
	 */
	public TreeNode(IPayload payload) {
		m_Node = s_Factory.createNode(payload);
	}

	/**
	 * Constructor with another INode the new one will be a clone of that
	 * 
	 * @param node
	 */
	public TreeNode(INode node) {
		this(node.getPayload());
		for (INode n : node.getOutgoingNodes()) {
			this.addOutgoingNode(n);
		}
	}

	/**
	 * Returns this tree as a String
	 * 
	 * @see java.lang.Object#toString()
	 */
	// @Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		// for (int i = 0; i < getPayload().getDepth(); ++i) {
		// sb.append('-');
		// }
		sb.append(this.getPayload().toString());
		sb.append('\n');
		for (INode node : this.getOutgoingNodes()) {
			sb.append(node.toString());
		}
		return sb.toString();
	}

	/**
	 * returns the line this token was found in (from Tree interface)
	 * 
	 * @return the line this token was found in
	 */
	public int getEndLine() {
		return getPayload().getLocation().getEndLine();
	}

	/**
	 * returns the line this token was found in (from Tree interface)
	 * 
	 * @return the line this token was found in
	 */
	public int getStartColumn() {
		return getPayload().getLocation().getStartColumn();
	}

	/**
	 * returns the line this token was found in (from Tree interface)
	 * 
	 * @return the line this token was found in
	 */
	public int getEndColumn() {
		return getPayload().getLocation().getEndColumn();
	}

	/**
	 * gets the text of this token (from Tree interface)
	 * 
	 * @return the text of this token
	 */
	public String getText() {
		return getPayload().getName();
	}

	/*
	 * Here starts INode
	 */

	// @Override
	public IPayload getPayload() {
		return this.m_Node.getPayload();
	}

	// //@Override
	// public void setDepth(int depth) {
	// this.m_Node.setDepth(depth);
	// }

	// @Override
	public boolean addIncomingNode(INode element) {
		return this.m_Node.addIncomingNode(element);
	}

	// @Override
	public boolean addOutgoingNode(INode element) {
		return this.m_Node.addOutgoingNode(element);
	}

	// @Override
	public List<INode> getIncomingNodes() {
		return this.m_Node.getIncomingNodes();
	}

	// @Override
	public List<INode> getOutgoingNodes() {
		return this.m_Node.getOutgoingNodes();
	}

	// @Override
	public void removeAllIncoming() {
		this.m_Node.removeAllIncoming();
	}

	// @Override
	public void removeAllOutgoing() {
		this.m_Node.removeAllOutgoing();
	}

	// @Override
	public boolean removeIncomingNode(INode element) {
		return this.m_Node.removeIncomingNode(element);
	}

	// @Override
	public boolean removeOutgoingNode(INode element) {
		return this.m_Node.removeOutgoingNode(element);
	}

	// //@Override
	// public Flags getFlags() {
	// return this.m_Node.getFlags();
	// }

	// @Override
	public boolean hasPayload() {
		return this.m_Node.hasPayload();
	}


}
