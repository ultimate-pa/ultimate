package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.CFGNodeAnnotations;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.AbstractNoEdgeNode;
import de.uni_freiburg.informatik.ultimate.model.Flags;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
//import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.Payload;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;

import org.apache.log4j.Logger;

public class CFGNode extends AbstractNoEdgeNode {

	private static final long serialVersionUID = 303486790200450017L;
	
	private List<INode> m_incoming = new ArrayList<INode>();
	private List<INode> m_outgoing = new ArrayList<INode>();
//	private Payload m_payload = new Payload();
	private boolean isLocated = false;
	//private boolean m_hasSuccessor = false;
	private static final Boolean debugMessages = false;
	private static Logger s_Logger = UltimateServices.getInstance().getLogger("CFGNode");
	
//	public CFGNode(INode parent) {
//		if (parent != null){
//			this.m_incoming.add(parent);
//		}
//	}
	
	public CFGNode(String name, ILocation loc) {
		setPayload(new Payload(loc, name, true));
	}
//	
//	public CFGNode() {
//		setPayload(new Payload());
//	}
//	
//	public CFGNode(Payload payload) {
////		this.m_payload = payload;
//		setPayload(payload);
//	}

	public CFGNodeAnnotations getCFGAnnotations() {
//		return (CFGNodeAnnotations) m_payload.getAnnotations().get("CFGBuilder");
		return (CFGNodeAnnotations) getPayload().getAnnotations().get("CFGBuilder");
	}
	
	public void addStatementToNode(Statement statement){
		if (!isLocated){
			isLocated = true;
		}
		if (getCFGAnnotations().getStatements().size() < 1) {
			getPayload().setLocation(statement.getLocation());
		}
		getCFGAnnotations().addStatement(statement);
	}
	
	//@Override
	public boolean addIncomingNode(INode element) {
		return this.m_incoming.add(element);
	}

	//@Override
	public boolean addOutgoingNode(INode element) {
//		this.m_payload.setChildCount(this.m_payload.getChildCount()+1);
		return this.m_outgoing.add(element);
	}

	//@Override
	public List<INode> getIncomingNodes() {
		return m_incoming;
	}

	//@Override
	public List<INode> getOutgoingNodes() {
//		if (debugMessages) s_Logger.info(m_payload.getName() + " has " + m_outgoing.size() + " outgoing edges!");
		if (debugMessages) s_Logger.info(getPayload().getName() + " has " + m_outgoing.size() + " outgoing edges!");
		return m_outgoing;
	}

	//@Override
	public void removeAllIncoming() {
		this.m_incoming.clear();
	}

	//@Override
	public void removeAllOutgoing() {
//		this.m_payload.setChildCount(0);
		this.m_outgoing.clear();
	}

	//@Override
	public boolean removeIncomingNode(INode element) {
		return this.m_incoming.remove(element);
	}

	//@Override
	public boolean removeOutgoingNode(INode element) {
//		this.m_payload.setChildCount(this.m_payload.getChildCount()-1);
		return this.m_outgoing.remove(element);
	}

	//@Override
	public void setDepth(int depth) {
		// TODO Auto-generated method stub

	}

	//@Override
	public Flags getFlags() {
		// TODO Auto-generated method stub
		return null;
	}

//	//@Override
//	public IPayload getPayload() {
//		return this.m_payload;
//	}
//
//	//@Override
//	public boolean hasPayload() {
//		return this.m_payload.isValue();
//	}
//
//	//@Override
//	public void setPayload(IPayload payload) {
//		this.m_payload = (Payload) payload;
//	}
//
	public void setName(String name){
		getPayload().setName(name);
	}

/*	public void setHasSuccessor(boolean hasSuccessor) {
		this.m_hasSuccessor = hasSuccessor;
	}

	public boolean getHasSuccessor() {
		return m_hasSuccessor;
	}*/
	
	public String toString() {
		if (getPayload() == null)
			return super.toString();
		else
			return getPayload().getName();
	}
}
