package local.stalin.plugins.generator.rcfgbuilder;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import local.stalin.model.AbstractEdgeNode;
import local.stalin.model.IAnnotations;
import local.stalin.model.IEdge;
import local.stalin.model.INode;
import local.stalin.model.Location;
import local.stalin.model.Payload;
import local.stalin.model.boogie.ast.AssumeStatement;
import local.stalin.model.boogie.ast.Statement;

/**
 * LocationNode, represents a location in a control flow graph.
 * Properties of the location are stored in a StateAnnot object.
 * @author heizmann@informatik.uni-freiburg.
 */

public class LocNode extends AbstractEdgeNode {

	private static final long serialVersionUID = 303486790200450017L;
	
	private List<IEdge> m_incoming = new ArrayList<IEdge>();
	private List<IEdge> m_outgoing = new ArrayList<IEdge>();
	
	private final IProgramState m_ProgramState;

	
	@SuppressWarnings("deprecation")
	public LocNode(String locName,	String procName, boolean isErrorLoc,
						Statement st, TransEdge trans) {
		RCfgState stateAnnot = 
				new RCfgState( new ProgramPoint(procName,locName, isErrorLoc));
		m_ProgramState = stateAnnot;
		HashMap<String, IAnnotations> annotations = 
				new HashMap<String, IAnnotations>();
		annotations.put(Activator.PLUGIN_ID, stateAnnot);
		
		Location loc = null;
		if (st !=null) {
			loc = new Location(st.getFilename(),"",st.getLineNr());
		}
		super.setPayload(new Payload(loc,locName));
		super.getPayload().setAnnotations(annotations);
		super.getPayload().setName(locName);
		
		if (trans != null) {
			trans.setTarget(this);
			this.addIncomingEdge(trans);
		}
	}
	
	public RCfgState getStateAnnot() {
		return ((RCfgState) getPayload().getAnnotations().get(Activator.PLUGIN_ID));
	}
	
	public ProgramPoint getProgramPoint() {
		return m_ProgramState.getProgramPoint();
	}
	
	public String getLocationName() {
		return super.getPayload().getName();
	}
	
//	public void addViolatingStatement(AssumeStatement st) {
//		Map<AssumeStatement, TransFormula> violations = getStateAnnot().getViolations();
//		if (violations == null) {
//			violations = new HashMap<AssumeStatement, TransFormula>();
//		}
//		violations.put(st, null);
//		getStateAnnot().setViolations(violations);
//	}
//	
//	public Collection<AssumeStatement> getViolatingStatements() {
//		Map<AssumeStatement, TransFormula> violations = getStateAnnot().getViolations();
//		if (violations == null) {
//			return null;
//		}
//		else {
//			return getStateAnnot().getViolations().keySet();
//		}
//	}

	@Override
	public boolean addIncomingEdge(IEdge element) {
//		if (!(element instanceof TransitionNode)) throw new IllegalArgumentException("A predecessor of a LocationNode has be a TransitionNode");
		return this.m_incoming.add(element);
	}
	
	@Override
	public boolean addOutgoingEdge(IEdge element) {
//		if (!(element instanceof TransitionNode)) throw new IllegalArgumentException("A successor of a LocationNode has be a TransitionNode");
		return this.m_outgoing.add(element);
	}

	@Override
	public boolean addIncomingEdge(INode src) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean addOutgoingEdge(INode target) {
		throw new UnsupportedOperationException();
	}

	@Override
	public List<IEdge> getIncomingEdges() {
		return m_incoming;
	}

	@Override
	public List<IEdge> getOutgoingEdges() {
		return m_outgoing;
	}

	@Override
	public void removeAllIncoming() {
		m_incoming.clear();
	}

	@Override
	public void removeAllOutgoing() {
		m_outgoing.clear();
	}

	@Override
	public boolean removeIncomingEdge(IEdge element) {
		return m_incoming.remove(element);
	}

	@Override
	public boolean removeOutgoingEdge(IEdge element) {
		return m_outgoing.remove(element);
	}

	@Override
	public String toString() {
		return getPayload().getName();
	}
	
	
}
