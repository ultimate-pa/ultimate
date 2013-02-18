package local.stalin.plugins.generator.rcfgbuilder;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import local.stalin.model.AbstractEdgeNode;
import local.stalin.model.IAnnotations;
import local.stalin.model.IEdge;
import local.stalin.model.INode;
import local.stalin.model.Payload;
import local.stalin.model.boogie.ast.ASTType;
import local.stalin.model.boogie.ast.Axiom;
import local.stalin.model.boogie.ast.Declaration;
import local.stalin.model.boogie.ast.Procedure;

/**
 * Root node in a STALIN Model of a program.
 * Information about about the program represented by this STALIN Model which
 * can not be expressed by the recursive control flow graph are stored in a
 * RootAnnot object stored in the Payload of this RootNode.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class RootNode extends AbstractEdgeNode {

	private static final long serialVersionUID = 303486790200450017L;
	
	private List<IEdge> m_incoming = new ArrayList<IEdge>();
	private List<IEdge> m_outgoing = new ArrayList<IEdge>();

	
	public RootNode(List<Declaration> declarations,
						   List<Axiom> axioms,
						   Map<String,Procedure> procedures,
						   Map<String,Procedure> implementations,
						   Map<String,Map<String,LocNode>> locNodes,
						   Map<String,LocNode> initialNodes,
						   Map<String,Map<String,ASTType>> modifiedVars,
						   Map<String,ASTType> globalVars,
						   boolean multipleStatementsPerTransition) {
		RootAnnot rootAnnot = new RootAnnot(declarations,
											axioms,
											procedures,
											implementations,
											locNodes,
											initialNodes,
											modifiedVars,
											globalVars,
											multipleStatementsPerTransition);
		HashMap<String, IAnnotations> annotations = new HashMap<String, IAnnotations>();
		annotations.put(Activator.PLUGIN_ID, rootAnnot);
		super.setPayload(new Payload(null,"RootNode"));
		super.getPayload().setAnnotations(annotations);
	}
	
	
	public RootAnnot getRootAnnot() {
		return ((RootAnnot) getPayload().getAnnotations().get(Activator.PLUGIN_ID));
	}
	

	@Override
	public boolean addIncomingEdge(IEdge element) {
		throw new UnsupportedOperationException("RootNode has no incoming edges");
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
