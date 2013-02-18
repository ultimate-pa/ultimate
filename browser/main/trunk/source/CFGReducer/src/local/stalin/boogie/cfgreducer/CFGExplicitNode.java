package local.stalin.boogie.cfgreducer;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.apache.log4j.Logger;

import local.stalin.SMTInterface.SMTInterface;
import local.stalin.core.api.StalinServices;
import local.stalin.logic.Atom;
import local.stalin.logic.Formula;
import local.stalin.logic.Theory;
import local.stalin.model.AbstractEdgeNode;
import local.stalin.model.IAnnotations;
import local.stalin.model.IEdge;
import local.stalin.model.INode;
import local.stalin.model.IPayload;
import local.stalin.model.Payload;

public class CFGExplicitNode extends AbstractEdgeNode {

	/**
	 * 
	 */
	private static final long serialVersionUID = -794904497079295989L;

	private List<IEdge> 				m_IncomingEdges		= new ArrayList<IEdge>();
	private List<IEdge> 				m_OutgoingEdges		= new ArrayList<IEdge>();
	private Payload 					m_Payload			= new Payload();
	private Theory 						m_Theory			= null;
	private static Logger				s_Logger			= StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	private static int					s_Counter			= 0;
	
	public CFGExplicitNode(Theory theory, Formula assertion){
		m_Theory = theory;
		HashMap<String, IAnnotations>	annotations = new HashMap<String, IAnnotations>();
		SMTNodeAnnotations				annotation	= new SMTNodeAnnotations();
		annotations.put("SMT", annotation);
		assertion = assertion != null? assertion: Atom.TRUE;
		annotation.setAssertion(assertion);
		annotation.setTheory(theory);
		m_Payload.setAnnotations(annotations);
	}
	
	public void resetCounter(){
		s_Counter = 0;
	}
	
	@Override
	public boolean addIncomingEdge(IEdge edge) {
		boolean result = m_IncomingEdges.add(edge);
		
		if (edge.getTarget() != this){
			edge.setTarget(this);
		}
		return result;
	}

	@Override
	public boolean addOutgoingEdge(IEdge edge) {
		boolean result = m_OutgoingEdges.add(edge);
		
		if (edge.getSource() != this){
			edge.setSource(this);
		}
		return result;
	}

	@Override
	public List<IEdge> getIncomingEdges() {
		return m_IncomingEdges;
	}

	@Override
	public List<IEdge> getOutgoingEdges() {
		return m_OutgoingEdges;
	}

	@Override
	public boolean removeIncomingEdge(IEdge edge) {
		boolean result = m_IncomingEdges.remove(edge);
		if (edge.getTarget() == this){
			edge.setTarget(null);
		}
		return result;
	}

	@Override
	public boolean removeOutgoingEdge(IEdge edge) {
		boolean result = m_OutgoingEdges.remove(edge);
		if (edge.getSource() == this){
			edge.setSource(null);
		}
		return result;
		}

	@Override
	public IPayload getPayload() {
		return m_Payload;
	}

	public SMTNodeAnnotations getSMTAnnotations(){
		return (SMTNodeAnnotations)m_Payload.getAnnotations().get("SMT");
	}
	
	public Theory getTheory(){
		return m_Theory;
	}
	
	@Override
	public boolean hasPayload() {
		return m_Payload.isValue();
	}

	@Override
	public void setPayload(IPayload payload) {
		m_Payload = (Payload)payload;
		//m_annotation = (SMTNodeAnnotations)m_payload.getAnnotations().get("SMT");
		if (getSMTAnnotations() == null){
			s_Logger.info("SMT annotations of node '" + this.getPayload().getName() + "' are null!");
		} else {
			setAssertion(getAssertion()); //Sets the assertion to TRUE if it's null
		}
	}
	
	public void addAssertion(Formula assertion){
		SMTNodeAnnotations annotation = getSMTAnnotations();
		assertion = assertion != null? assertion: Atom.TRUE;
		annotation.setAssertion(m_Theory.and(annotation.getAssertion(), assertion));
	}
	
	public Formula getAssertion(){
		return getSMTAnnotations() != null? getSMTAnnotations().getAssertion(): Atom.TRUE;
	}
	
	public void setAssertion(Formula assertion){
		getSMTAnnotations().setAssertion(assertion != null? assertion: Atom.TRUE);
	}

	@Override
	public boolean addIncomingEdge(INode src) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean addOutgoingEdge(INode target) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void removeAllIncoming() {
		List<IEdge> tmp = new ArrayList<IEdge>();
		tmp.addAll(m_IncomingEdges);
		for (IEdge iedge: tmp){
			CFGEdge edge = (CFGEdge)iedge;
			edge.deleteEdge();
		}
	}

	@Override
	public void removeAllOutgoing() {
		List<IEdge> tmp = new ArrayList<IEdge>();
		tmp.addAll(m_OutgoingEdges);
		for (IEdge iEdge: tmp){
			CFGEdge edge = (CFGEdge)iEdge;
			edge.deleteEdge();
		}
	}
	
	public CFGExplicitNode copyWithoutEdges(){
		return copyWithoutEdges(false);
	}
	
	public CFGExplicitNode copyWithoutEdgesWithSSA(){
		return copyWithoutEdges(true);
	}
	
	private CFGExplicitNode copyWithoutEdges(boolean usingSSA){
		CFGExplicitNode newCFGExplicitNode 	= new CFGExplicitNode(m_Theory, getAssertion());
		Payload newPayload = usingSSA? PayloadModifier.copyPayloadWithSSA(m_Payload): PayloadModifier.copyPayload(m_Payload);
		newPayload.setName(m_Payload.getName() + "_" + s_Counter++);
		newCFGExplicitNode.setPayload(newPayload);
		return newCFGExplicitNode;
	}
	
	public void copyAllPredecessorsFromNode(INode node){
		for (IEdge iEdge: node.getIncomingEdges()){
			CFGEdge edge = (CFGEdge)iEdge;
			CFGEdge newEdge = edge.copyWithoutNodes();
			newEdge.setSource(edge.getSource());
			newEdge.setTarget(this);
		}
	}
	
	public void copyAllSuccessorsFromNode(INode node){
		boolean UseSSA = getSMTAnnotations().m_clonedUsingSSA;
		for (IEdge iEdge: node.getOutgoingEdges()){
			CFGEdge edge = (CFGEdge)iEdge;
			CFGEdge newEdge = UseSSA? edge.copyWithoutNodesUsingSSAMapping(getSMTAnnotations().getSSAMapping()): edge.copyWithoutNodes();
			newEdge.setSource(this);
			newEdge.setTarget(edge.getTarget());
		}
	}
	
	public boolean cleanUnsatisfiableEdges(){
		ArrayList<CFGEdge> unsatEdges = new ArrayList<CFGEdge>();
		for (IEdge iEdge: m_OutgoingEdges){
			CFGEdge edge = (CFGEdge)iEdge;
			int result = edge.checkSatisfiability();
			if (result == SMTInterface.SMT_UNSAT){
				unsatEdges.add(edge);
			} else if (result == SMTInterface.SMT_ERROR){
				return false;
			}
		}
		for (IEdge iEdge: m_IncomingEdges){
			CFGEdge edge = (CFGEdge)iEdge;
			int result = edge.checkSatisfiability();
			if (result == SMTInterface.SMT_UNSAT){
				unsatEdges.add(edge);
			} else if (result == SMTInterface.SMT_ERROR){
				return false;
			}
		}
		for (CFGEdge edge: unsatEdges){
			edge.deleteEdge();
		}
		return true;
	}
	
	public String toString(){
		return getPayload().getName();
	}
}
