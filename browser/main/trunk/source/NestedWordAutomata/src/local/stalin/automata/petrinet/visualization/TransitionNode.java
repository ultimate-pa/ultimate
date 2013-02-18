package local.stalin.automata.petrinet.visualization;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import local.stalin.automata.Activator;
import local.stalin.model.AbstractNoEdgeNode;
import local.stalin.model.DefaultAnnotations;
import local.stalin.model.IAnnotations;
import local.stalin.model.INode;
import local.stalin.model.Payload;

/**
 * STALIN model of a PetriNet transition.
 * @author heizmann@informatik.uni-freiburg.de 
 */

public class TransitionNode extends AbstractNoEdgeNode {

	private static final long serialVersionUID = -2531826841396458461L;
	private List<INode> m_Incoming = new ArrayList<INode>();
	private List<INode> m_Outgoing = new ArrayList<INode>();
	
	
	public TransitionNode(Object symbol) {
		
		Payload payload = new Payload();
		DefaultAnnotations thisPluginsAnnotations = new DefaultAnnotations();
		HashMap<String,IAnnotations> annotations = 
				new HashMap<String,IAnnotations>();
		annotations.put(Activator.PLUGIN_ID, thisPluginsAnnotations);
		
		if (symbol instanceof IAnnotations) {
			thisPluginsAnnotations.put("Symbol", (IAnnotations) symbol);

		}
		if (symbol != null) {
			payload.setName(symbol.toString());
		}
		payload.setAnnotations(annotations);
		super.setPayload(payload);
	}


	public String toString() {
		return super.getPayload().getName();
	}


	@Override
	public boolean addIncomingNode(INode element) {
		return m_Incoming.add(element);
	}


	@Override
	public boolean addOutgoingNode(INode element) {
		return m_Outgoing.add(element);
	}


	@Override
	public List<INode> getIncomingNodes() {
		return m_Incoming;
	}


	@Override
	public List<INode> getOutgoingNodes() {
		return m_Outgoing;
	}


	@Override
	public void removeAllIncoming() {
		throw new UnsupportedOperationException();
	}


	@Override
	public void removeAllOutgoing() {
		throw new UnsupportedOperationException();
	}


	@Override
	public boolean removeIncomingNode(INode element) {
		throw new UnsupportedOperationException();
	}


	@Override
	public boolean removeOutgoingNode(INode element) {
		throw new UnsupportedOperationException();
	}


}
