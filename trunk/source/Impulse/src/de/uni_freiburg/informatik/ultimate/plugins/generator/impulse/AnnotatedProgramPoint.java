package de.uni_freiburg.informatik.ultimate.plugins.generator.impulse;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.AbstractNoEdgeNode;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.Predicate;

public class AnnotatedProgramPoint extends AbstractNoEdgeNode{

	/**
	 * 
	 */
	private static final long serialVersionUID = -4398335480646555023L;
	
	private Predicate m_predicate;
	private ProgramPoint m_programPoint;
	
	private HashMap<AnnotatedProgramPoint, CodeBlock> m_incomingEdges =
			new HashMap<AnnotatedProgramPoint, CodeBlock>();
	private HashMap<AnnotatedProgramPoint, CodeBlock> m_outgoingEdges =
			new HashMap<AnnotatedProgramPoint, CodeBlock>();
	
	private boolean m_isPseudoErrorLocation = false;
	
	public AnnotatedProgramPoint(Predicate predicate, ProgramPoint programPoint) {
		m_predicate = predicate;
		m_programPoint = programPoint;
	}
	
	public AnnotatedProgramPoint(Predicate predicate, ProgramPoint programPoint, boolean isPseudoEL) {
		assert isPseudoEL; //only then this constructor is needed
		m_isPseudoErrorLocation = isPseudoEL;
		m_predicate = predicate;
		m_programPoint = programPoint;
	}

	public Predicate getPredicate() {
		return m_predicate;
	}
	
	public void setPredicate(Predicate predicate) {
		m_predicate = predicate;
	}
	
	public boolean isErrorLocation() {
		return m_programPoint.isErrorLocation() ||
				m_isPseudoErrorLocation;
	}
	
	public boolean isPseudoErrorLocation() {
		return m_isPseudoErrorLocation;
	}
	
	public CodeBlock getOutgoingCodeBlockOf(AnnotatedProgramPoint pp) {
		return m_outgoingEdges.get(pp);
	}
	
	public CodeBlock getIncomingCodeBlockOf(AnnotatedProgramPoint pp) {
		return m_incomingEdges.get(pp);
	}
	
	public ProgramPoint getProgramPoint() {
		return m_programPoint;
	}
	
	
	//---------- interface stuff ---------------

	@Override
	public List<INode> getIncomingNodes() {
		return new ArrayList<INode>(m_incomingEdges.keySet());
	}

	@Override
	public List<INode> getOutgoingNodes() {
		return new ArrayList<INode>(m_outgoingEdges.keySet());
	}

	@Override
	public boolean addOutgoingNode(INode element) {
		return false; //TODO ??
	}

	@Override
	public boolean addIncomingNode(INode element) {
		return false; //TODO ??
	}

	public void addOutgoingNode(AnnotatedProgramPoint app, CodeBlock cd) {
		m_outgoingEdges.put(app, cd);
	}

	public void addIncomingNode(AnnotatedProgramPoint app, CodeBlock cd) {
		m_incomingEdges.put(app, cd);
	}
	
	public void removeOutgoingNode(AnnotatedProgramPoint app) {
		m_outgoingEdges.remove(app);
	}

	public void removeIncomingNode(AnnotatedProgramPoint app) {
		m_incomingEdges.remove(app);
	}
	
	@Override
	public boolean removeOutgoingNode(INode element) {
		return m_outgoingEdges.remove(element)!=null?true:false;
	}

	@Override
	public boolean removeIncomingNode(INode element) {
		return m_incomingEdges.remove(element)!=null?true:false;
	}

	@Override
	public void removeAllIncoming() {
		m_incomingEdges.clear();
	}

	@Override
	public void removeAllOutgoing() {
		m_outgoingEdges.clear();
	}
	
	public IPayload getPayload() {
		return m_programPoint.getPayload();
	}
	
	public String toString() {
		return m_isPseudoErrorLocation ? "PEL" + m_predicate.toString() : m_predicate.toString();
	}
}
