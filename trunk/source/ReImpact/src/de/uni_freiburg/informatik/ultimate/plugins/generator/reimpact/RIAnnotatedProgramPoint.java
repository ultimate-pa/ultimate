package de.uni_freiburg.informatik.ultimate.plugins.generator.reimpact;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.AbstractNoEdgeNode;
import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.structure.BaseLabeledEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;

public class RIAnnotatedProgramPoint extends BaseLabeledEdgesMultigraph<RIAnnotatedProgramPoint, CodeBlock> {

	private static final long serialVersionUID = -4398335480646555023L;
	
	private IPredicate m_predicate;
	private ProgramPoint m_programPoint;
	
	public RIAnnotatedProgramPoint(IPredicate predicate, ProgramPoint programPoint) {
		m_predicate = predicate;
		m_programPoint = programPoint;
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
	
	protected void addOutgoingNode(RIAnnotatedProgramPoint node, CodeBlock label) {
		this.mOutgoingNodes.add(node);
		this.mOutgoingEdgeLabels.put(node, label);
		node.mIncomingNodes.add(this);
	}

	protected void removeOutgoingNode(RIAnnotatedProgramPoint node) {
		mOutgoingNodes.remove(node);
		mOutgoingEdgeLabels.remove(node);
		node.mIncomingNodes.remove(this);
	}
	
	protected void addIncomingNode(RIAnnotatedProgramPoint node, CodeBlock label) {
		this.mIncomingNodes.add(node);
		node.mOutgoingEdgeLabels.put(node, label);
		node.mOutgoingNodes.add(this);
	}

	protected void removeIncomingNode(RIAnnotatedProgramPoint node) {
		mIncomingNodes.remove(node);
		node.mOutgoingNodes.remove(this);
		node.mOutgoingEdgeLabels.remove(this);
	}
	
	public IPayload getPayload() {
		return m_programPoint.getPayload();
	}
	
	public String toString() {
		return m_programPoint.toString(); //+ ":" + m_predicate.toString();
	}
}
