package de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.Event;
import de.uni_freiburg.informatik.ultimate.model.AbstractNoEdgeNode;
import de.uni_freiburg.informatik.ultimate.model.DefaultAnnotations;
import de.uni_freiburg.informatik.ultimate.model.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.Payload;

/**
 * Ultimate model of a OcurrenceNet event.
 * @author heizmann@informatik.uni-freiburg.de 
 */

public class EventNode<S,C> extends AbstractNoEdgeNode {

	private static final long serialVersionUID = -2531826841396458461L;
	private List<INode> m_Incoming = new ArrayList<INode>();
	private List<INode> m_Outgoing = new ArrayList<INode>();
	
	
	public EventNode(Event<S,C> event) {
		
		Payload payload = new Payload();
		DefaultAnnotations annot = new DefaultAnnotations();
		annot.put("Transition",event.getTransition());
		annot.put("Companion", event.getCompanion());
		annot.put("Ancestors", event.getAncestors());
		annot.put("ByLocalConfigurationRepresentedMarking",event.getMark());
	
		HashMap<String,IAnnotations> annotations = 
				new HashMap<String,IAnnotations>();
		annotations.put(Activator.PLUGIN_ID, annot);
		
		S symbol = event.getTransition().getSymbol();
		if (symbol instanceof IAnnotations) {
			annot.put("Symbol", (IAnnotations) symbol);

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
