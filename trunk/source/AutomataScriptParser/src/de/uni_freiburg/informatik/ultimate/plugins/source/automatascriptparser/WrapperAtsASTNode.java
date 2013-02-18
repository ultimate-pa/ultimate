package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.structure.IAST;
import de.uni_freiburg.informatik.ultimate.model.structure.IWalkable;


public class WrapperAtsASTNode implements INode {

	/**
	 * 
	 */
	private static final long serialVersionUID = -7896223145938713082L;
    
	private IAST atsASTNode;
	
	public WrapperAtsASTNode(IAST atsASTNode) {
		this.atsASTNode = atsASTNode;
	}

	@Override
	public IPayload getPayload() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean hasPayload() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public List<INode> getIncomingNodes() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public List<INode> getOutgoingNodes() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean addOutgoingNode(INode element) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean addIncomingNode(INode element) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean removeOutgoingNode(INode element) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean removeIncomingNode(INode element) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public List<IEdge> getIncomingEdges() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public List<IEdge> getOutgoingEdges() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean addOutgoingEdge(IEdge element) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean addIncomingEdge(IEdge element) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean addOutgoingEdge(INode target) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean addIncomingEdge(INode src) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean removeOutgoingEdge(IEdge element) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean removeIncomingEdge(IEdge element) {
		// TODO Auto-generated method stub
		return false;
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
	public int getChildCount() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public List<IWalkable> getSuccessors() {
		// TODO Auto-generated method stub
		return null;
	}

}
