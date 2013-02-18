package de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.Condition;
import de.uni_freiburg.informatik.ultimate.model.AbstractNoEdgeNode;
import de.uni_freiburg.informatik.ultimate.model.DefaultAnnotations;
import de.uni_freiburg.informatik.ultimate.model.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.Payload;

/**
 * Ultimate model of a OccurenceNet condition.
 * @author heizmann@informatik.uni-freiburg.de 
 */

public class ConditionNode<S,C> extends AbstractNoEdgeNode {
	/**
	 * 
	 */
	private static final long serialVersionUID = 264254789648279608L;
	private List<INode> m_Incoming = new ArrayList<INode>();
	private List<INode> m_Outgoing = new ArrayList<INode>();
	
	public ConditionNode(Condition<S,C> condition, BranchingProcess<S,C> bc) {
		
		Payload payload = new Payload();
		DefaultAnnotations annot = new DefaultAnnotations();
		annot.put("Condition",condition.toString());
		annot.put("CorrespondingPlace",condition.getPlace());
		annot.put("NumberSuccesorEvents", condition.getSuccessorEvents().size());
		annot.put("AllConditionsInCoRelation", allConditionsInCoRelation(condition,bc));
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
	
	private ArrayList<Condition<S,C>> allConditionsInCoRelation(Condition<S,C> condition, BranchingProcess<S,C> bc) {
		ArrayList<Condition<S,C>> conditionsInCoRelation = new ArrayList<Condition<S,C>>();
		for (Condition<S,C> c : bc.getConditions()) {
			if (bc.isInCoRelation(condition, c)) {
				conditionsInCoRelation.add(c);
			}
		}
		return conditionsInCoRelation;
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
