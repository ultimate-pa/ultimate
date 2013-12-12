package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.staticutils.PayloadModifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.transfomers.SubstituteTermTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SMTNodeAnnotations;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.AbstractEdgeNode;
import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.Payload;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;

public class CFGExplicitNode extends AbstractEdgeNode {

	/**
	 * 
	 */
	private static final long serialVersionUID = -794904497079295989L;

	private List<IEdge> 				m_IncomingEdges		= new ArrayList<IEdge>();
	private List<IEdge> 				m_OutgoingEdges		= new ArrayList<IEdge>();
	private Payload 					m_Payload			= new Payload();
	private Script 						m_Script			= null;

	private HashMap<Term,Term> 			m_substitutionMap	= new HashMap<Term, Term>();
	private static Logger				s_Logger			= UltimateServices.getInstance().getLogger("CFGExplicitNode");
	private static int					s_Counter			= 0;
	
	/**
	 * copy constructor 
	 * @param useSsa 
	 */
	public CFGExplicitNode(CFGExplicitNode original, boolean useSsa) {
		m_Script = original.getScript();
		if (useSsa)
			m_Payload = PayloadModifier.copyPayloadWithSSA(original.getPayload());
		else
			m_Payload = PayloadModifier.copyPayload(original.getPayload());
	}
	
	public CFGExplicitNode(Script script, Term assertion){
		m_Script = script;
		HashMap<String, IAnnotations>	annotations = new HashMap<String, IAnnotations>();
		SMTNodeAnnotations				annotation	= new SMTNodeAnnotations();
		annotations.put("SMT", annotation);
		assertion = assertion != null? assertion: m_Script.term("true");
		annotation.setAssertion(assertion);
		annotation.setScript(script);
		m_Payload.setAnnotations(annotations);
	}
	
	public void setSubstitution(HashMap<Term,Term> substitutionMap) {
		m_substitutionMap = substitutionMap;
	}
	
	public void addSubstitution(HashMap<Term,Term> substitutionMap) {
		m_substitutionMap.putAll(substitutionMap);
	}
	
	public HashMap<Term,Term> getSubstitutionMap() {
		return m_substitutionMap;
	}
	
	public void addSubstitution(Term term, Term substitute) {
		for(Entry<Term, Term> entry: m_substitutionMap.entrySet()) {
			if(entry.getValue().equals(term)) {
				m_substitutionMap.put(entry.getKey(), substitute);
			}
		}
		m_substitutionMap.put(term, substitute);
	}
	
	public void applySubstitution() {
		if(m_substitutionMap.isEmpty()) {
			return;
		}
		SubstituteTermTransformer subTermTransformer =
				new SubstituteTermTransformer();
		this.setAssertion(subTermTransformer.substitute(
				getSMTAnnotations().getAssertion(), m_substitutionMap));
		m_substitutionMap = new HashMap<Term, Term>();
		for(IEdge iEdge: getOutgoingEdges()) {
			CFGEdge edge = (CFGEdge) iEdge;
			edge.applySubstitution();
		}
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
//		if (edge.getTarget() == this){
//			edge.setTarget(null);
//		}
		return result;
	}

	@Override
	public boolean removeOutgoingEdge(IEdge edge) {
		boolean result = m_OutgoingEdges.remove(edge);
//		if (edge.getSource() == this){
//			edge.setSource(null);
//		}
		return result;
	}

	@Override
	public IPayload getPayload() {
		return m_Payload;
	}

	public SMTNodeAnnotations getSMTAnnotations(){
		return (SMTNodeAnnotations)m_Payload.getAnnotations().get("SMT");
	}
	
	public Script getScript(){
		return m_Script;
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
	
	public void addAssertion(Term assertion){
		SMTNodeAnnotations annotation = getSMTAnnotations();
		assertion = assertion != null? assertion: m_Script.term("true");
		setAssertion(Util.and(m_Script,  annotation.getAssertion(), assertion));
	}
	
	public Term getAssertion(){
		return getSMTAnnotations() != null? getSMTAnnotations().getAssertion(): m_Script.term("true");
	}
	
	public void setAssertion(Term assertion){
		getSMTAnnotations().setAssertion(assertion != null? assertion: m_Script.term("true"));
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
		CFGExplicitNode newCFGExplicitNode 	= new CFGExplicitNode(m_Script, getAssertion());
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
			CFGEdge newEdge = UseSSA? 
					edge.copyWithoutNodesUsingSSAMapping(getSMTAnnotations().getSSAMapping()): 
						edge.copyWithoutNodes();
			newEdge.setSource(this);
			newEdge.setTarget(edge.getTarget());
		}
	}
	
	public boolean cleanUnsatisfiableEdges(){
		ArrayList<CFGEdge> unsatEdges = new ArrayList<CFGEdge>();
		
		for (IEdge iEdge: m_IncomingEdges){
			CFGEdge edge = (CFGEdge)iEdge;
			LBool result;
			try {
				result = edge.checkSatisfiability();
			} catch (SMTLIBException e) {
				s_Logger.info("Failed cleaning unsat incoming edges of node " + this.getPayload().getName());
				s_Logger.info(e);
				return false;
			}
			if (result == LBool.UNSAT){ // -1 is unsat
				unsatEdges.add(edge);
			}
		}
		boolean deleteAllOutgoing = false;
		if (unsatEdges.size() == m_IncomingEdges.size()){
			deleteAllOutgoing = true;
		}
		
		for (IEdge iEdge: m_OutgoingEdges){
			CFGEdge edge = (CFGEdge)iEdge;
			LBool result;
			try {
				result = edge.checkSatisfiability();
			} catch (SMTLIBException e) {
				s_Logger.info("Failed cleaning unsat outgoing edges of node " + this.getPayload().getName());
				s_Logger.info(e);
				return false;
			}
			if (result == LBool.UNSAT || deleteAllOutgoing){
				unsatEdges.add(edge);
			}
		}
		
		for (CFGEdge edge: unsatEdges){
			edge.deleteEdge();
		}
		return true;
	}
	
	public boolean cleanUnsatisfiableIncomingEdges(){
		ArrayList<CFGEdge> unsatEdges = new ArrayList<CFGEdge>();
		
		for (IEdge iEdge: m_IncomingEdges){
			CFGEdge edge = (CFGEdge)iEdge;
			LBool result;
			try {
				result = edge.checkSatisfiability();
			} catch (SMTLIBException e) {
				s_Logger.info("Failed cleaning unsat incoming edges of node " + this.getPayload().getName());
				s_Logger.info(e);
				return false;
			}
			if (result == LBool.UNSAT){ // -1 is unsat
				unsatEdges.add(edge);
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
