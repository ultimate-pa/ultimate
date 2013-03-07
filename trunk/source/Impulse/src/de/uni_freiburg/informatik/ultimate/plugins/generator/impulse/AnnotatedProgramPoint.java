package de.uni_freiburg.informatik.ultimate.plugins.generator.impulse;

import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.structure.BaseLabeledEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;

public class AnnotatedProgramPoint extends BaseLabeledEdgesMultigraph<AnnotatedProgramPoint, CodeBlock> {

	private static final long serialVersionUID = -4398335480646555023L;
	
	private IPredicate m_predicate;
	private ProgramPoint m_programPoint;
	
	boolean m_isPseudoErrorLocation = false;
	
	private HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>> m_outgoingReturnAppToCallPreds;
	
	public AnnotatedProgramPoint(IPredicate predicate, ProgramPoint programPoint) {
		m_predicate = predicate;
		m_programPoint = programPoint;
	}
	
	public AnnotatedProgramPoint(IPredicate predicate, ProgramPoint programPoint, boolean isPEL) {
		m_predicate = predicate;
		m_programPoint = programPoint;
		m_isPseudoErrorLocation = isPEL;
	}

	public IPredicate getPredicate() {
		return m_predicate;
	}
	
	public void setPredicate(IPredicate predicate) {
		m_predicate = predicate;
	}
	
	public boolean isErrorLocation() {
		return m_programPoint.isErrorLocation();
	}
	
	public ProgramPoint getProgramPoint() {
		return m_programPoint;
	}
	
	public void addOutgoingNode(AnnotatedProgramPoint node, CodeBlock label) {
		this.mOutgoingNodes.add(node);
		this.mOutgoingEdgeLabels.put(node, label);
		node.mIncomingNodes.add(this);
	}

	public void removeOutgoingNode(AnnotatedProgramPoint node) {
		mOutgoingNodes.remove(node);
		mOutgoingEdgeLabels.remove(node);
		node.mIncomingNodes.remove(this);
	}
	
	public void addIncomingNode(AnnotatedProgramPoint node, CodeBlock label) {
		this.mIncomingNodes.add(node);
		node.mOutgoingEdgeLabels.put(node, label);
		node.mOutgoingNodes.add(this);
	}

	public void removeIncomingNode(AnnotatedProgramPoint node) {
		mIncomingNodes.remove(node);
		node.mOutgoingNodes.remove(this);
		node.mOutgoingEdgeLabels.remove(this);
	}
	
	public void addOutGoingReturnCallPred(AnnotatedProgramPoint target, AnnotatedProgramPoint callPred) {
		assert mOutgoingEdgeLabels.get(target) instanceof Return;
		
		if (m_outgoingReturnAppToCallPreds == null)
			m_outgoingReturnAppToCallPreds = new HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>>();
		
		if (m_outgoingReturnAppToCallPreds.get(target) == null)
			m_outgoingReturnAppToCallPreds.put(target, new HashSet<AnnotatedProgramPoint>());
		
		m_outgoingReturnAppToCallPreds.get(target).add(callPred);
	}
	
	public void removeOutgoingReturnCallPred(AnnotatedProgramPoint target, AnnotatedProgramPoint callPred) {
		assert mOutgoingEdgeLabels.get(target) instanceof Return;
		assert m_outgoingReturnAppToCallPreds != null && m_outgoingReturnAppToCallPreds.get(target) != null;
		
		m_outgoingReturnAppToCallPreds.get(target).remove(callPred);		
	}
	
	public boolean outGoingReturnAppToCallPredContains(AnnotatedProgramPoint target, AnnotatedProgramPoint callPred) {
		assert mOutgoingEdgeLabels.get(target) instanceof Return;
		assert m_outgoingReturnAppToCallPreds != null; 
		
		return m_outgoingReturnAppToCallPreds.get(target).contains(callPred);
	}
	
	public IPayload getPayload() {
		return m_programPoint.getPayload();
	}
	
	public String toString() {
		return m_programPoint.toString(); //+ ":" + m_predicate.toString();
	}

	public void setIsPseudoErrorLocation(boolean value) {
		m_isPseudoErrorLocation = value;
	}
	
	public boolean isPseudoErrorLocation() {
		return m_isPseudoErrorLocation;
	}
}
