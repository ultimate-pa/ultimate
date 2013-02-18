package de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.model.AbstractNoEdgeNode;
import de.uni_freiburg.informatik.ultimate.model.DefaultAnnotations;
import de.uni_freiburg.informatik.ultimate.model.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.Payload;

/**
 * Ultimate model of a PetriNet place.
 * @author heizmann@informatik.uni-freiburg.de 
 */

public class PlaceNode extends AbstractNoEdgeNode {
	/**
	 * 
	 */
	private static final long serialVersionUID = 264254789648279608L;
	private List<INode> m_Incoming = new ArrayList<INode>();
	private List<INode> m_Outgoing = new ArrayList<INode>();
	
	public PlaceNode(Place place, 
							Collection<String> participatedAcceptingMarkings) {
		
		Payload payload = new Payload();
		DefaultAnnotations thisPluginsAnnotations = new DefaultAnnotations();
		thisPluginsAnnotations.put("accepting markings containing this place",
				participatedAcceptingMarkings);
		thisPluginsAnnotations.put("toString",place.toString());
		thisPluginsAnnotations.put("hashCode",place.hashCode());
		HashMap<String,IAnnotations> annotations = 
				new HashMap<String,IAnnotations>();
		annotations.put(Activator.PLUGIN_ID, thisPluginsAnnotations);
		
		if (place.getContent() instanceof IAnnotations) {
			thisPluginsAnnotations.put("Content", (IAnnotations) place.getContent());

		}
		if (place.getContent() != null) {
			payload.setName(place.getContent().toString());
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
