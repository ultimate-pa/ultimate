package local.stalin.automata.petrinet.visualization;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import local.stalin.automata.Activator;
import local.stalin.automata.petrinet.jan.ICondition;
import local.stalin.model.AbstractNoEdgeNode;
import local.stalin.model.DefaultAnnotations;
import local.stalin.model.IAnnotations;
import local.stalin.model.INode;
import local.stalin.model.Payload;

/**
 * STALIN model of a OccurenceNet condition.
 * @author heizmann@informatik.uni-freiburg.de 
 */

public class ConditionNode<S,C> extends AbstractNoEdgeNode {
	/**
	 * 
	 */
	private static final long serialVersionUID = 264254789648279608L;
	private List<INode> m_Incoming = new ArrayList<INode>();
	private List<INode> m_Outgoing = new ArrayList<INode>();
	
	public ConditionNode(ICondition<S,C> condition) {
		
		Payload payload = new Payload();
		DefaultAnnotations annot = new DefaultAnnotations();
		annot.put("Place",condition.getPlace());
		HashMap<String,IAnnotations> annotations = 
				new HashMap<String,IAnnotations>();
		annotations.put(Activator.PLUGIN_ID, annot);
		
		C content = condition.getPlace().getContent();
		if (content instanceof IAnnotations) {
			annot.put("Content", (IAnnotations) content);

		}
		if (content != null) {
			payload.setName(content.toString());
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
