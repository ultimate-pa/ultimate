/**
 * 
 */
package local.stalin.plugins.generator.lazyabstraction;

import java.util.HashMap;

import local.stalin.SMTInterface.SMTInterface;
import local.stalin.boogie.cfgreducer.SMTEdgeAnnotations;
import local.stalin.boogie.cfgreducer.SMTNodeAnnotations;
import local.stalin.logic.Atom;
import local.stalin.logic.Formula;
import local.stalin.logic.Theory;
import local.stalin.model.IAnnotations;
import local.stalin.model.IEdge;
import local.stalin.model.INode;
import local.stalin.model.IPayload;
import local.stalin.model.Payload;

/**
 * @author alexander
 *
 */
public class UnwindingEdge implements IEdge {

	UnwindingNode m_source;
	UnwindingNode m_target;
	Theory m_theory;
	
	Payload m_payload = new Payload();
//	private static SMTInterface s_SMTInterface	= null;
	
	/**
	 * 
	 */
	private static final long serialVersionUID = -2040731502664665745L;

//	/**
//	 * 
//	 */
//	public UnwindingEdge() {
//		// TODO Auto-generated constructor stub
//	}

	//TODO: ev. Konstruktoren zusammenfassen, um redundanten code zu minimieren..
	public UnwindingEdge(Theory theory, UnwindingNode src,
			UnwindingNode trg) {
		
		//taken from CFGEdge
		m_source = src;
		m_target = trg;
		m_theory = theory;
		HashMap<String, IAnnotations>	annotations = new HashMap<String, IAnnotations>();
		SMTEdgeAnnotations				annotation	= new SMTEdgeAnnotations();
		annotations.put("SMT", annotation);
		annotation.setAssumption(Atom.TRUE);
		annotation.setTheory(m_theory);
		m_payload.setAnnotations(annotations);
		m_payload.setName(this.getSMTAnnotations().getAssumption().toString());
	}

	
	/*
	 * constructor for an edge to an error location: the assertion coming from the node has to be the negated assumption of 
	 * such an edge
	 */
	public UnwindingEdge(Theory theory, SMTNodeAnnotations nodeAnnotations, UnwindingNode src,
			UnwindingNode trg, boolean negateAssertion) {
		
		//taken from CFGEdge
		m_source = src;
		m_target = trg;
		m_theory = theory;
		HashMap<String, IAnnotations>	annotations = new HashMap<String, IAnnotations>();
		SMTEdgeAnnotations				annotation	= new SMTEdgeAnnotations();
		annotations.put("SMT", annotation);
		if(negateAssertion) { //vermutlich immer wahr, aber der Verständlichkeit wegen drin
			annotation.setAssumption(m_theory.not(nodeAnnotations.getAssertion()));	
		}
		else {
			annotation.setAssumption(nodeAnnotations.getAssertion());	
		}			 
		annotation.setInVars(nodeAnnotations.getInVars());
		annotation.setSSAMapping(nodeAnnotations.getSSAMapping());
		annotation.setVars(nodeAnnotations.getVars());
		annotation.setOutVars(nodeAnnotations.getOldVars()); //TODO: out =^ old?????
		annotation.setTheory(m_theory);
		m_payload.setAnnotations(annotations);
		m_payload.setName(this.getSMTAnnotations().getAssumption().toString());
	}
	
	public UnwindingEdge(Theory theory, SMTEdgeAnnotations edgeAnnotations, UnwindingNode src,
			UnwindingNode trg) {
		
		//taken from CFGEdge
		m_source = src;
		m_target = trg;
		m_theory = theory;
		HashMap<String, IAnnotations>	annotations = new HashMap<String, IAnnotations>();
		SMTEdgeAnnotations				annotation	= new SMTEdgeAnnotations();
		annotations.put("SMT", annotation);
		annotation.setAssumption(edgeAnnotations.getAssumption());
		annotation.setInVars(edgeAnnotations.getInVars());
		annotation.setVars(edgeAnnotations.getVars());
		annotation.setOutVars(edgeAnnotations.getOutVars()); 
		annotation.setTheory(m_theory);
		m_payload.setAnnotations(annotations);
		m_payload.setName(this.getSMTAnnotations().getAssumption().toString());
	}
	
	/* (non-Javadoc)
	 * @see local.stalin.model.IEdge#getSource()
	 */
	@Override
	public INode getSource() {
		return m_source;
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.IEdge#getTarget()
	 */
	@Override
	public INode getTarget() {
		return m_target;
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.IEdge#setSource(local.stalin.model.INode)
	 */
	@Override
	public void setSource(INode source) {
		if(!(source instanceof UnwindingNode))
		{
			// TODO passende Exception werfen
		}
		m_source = (UnwindingNode) source;
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.IEdge#setTarget(local.stalin.model.INode)
	 */
	@Override
	public void setTarget(INode target) {
		if(!(target instanceof UnwindingNode))
		{
			// TODO passende Exception werfen
		}
		m_target = (UnwindingNode) target;
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.IElement#getPayload()
	 */
	@Override
	public IPayload getPayload() {
		return m_payload;
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.IElement#hasPayload()
	 */
	@Override
	public boolean hasPayload() {
		// TODO Auto-generated method stub
		return false;
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.IElement#setPayload(local.stalin.model.IPayload)
	 */
	@Override
	public void setPayload(IPayload payload) {
		m_payload = (Payload) payload;
	}

//	public Object getSMTAnnotations() {
//		return m_payload.getAnnotations().get("SMT"); 
//	}

	public SMTEdgeAnnotations getSMTAnnotations(){
		return (SMTEdgeAnnotations)m_payload.getAnnotations().get("SMT");
	}


	@Override
	public String toString() {
//		return super.toString();
		return m_payload.getName();
	}
	
	
}
