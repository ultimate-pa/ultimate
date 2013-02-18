package local.stalin.automata.petrinet.visualization;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

import local.stalin.automata.petrinet.jan.ICondition;
import local.stalin.automata.petrinet.jan.IEvent;
import local.stalin.automata.petrinet.jan.IOccurrenceNet;
import local.stalin.model.INode;

public class OccurenceNetToStalinModel<S, C> {
	
	
	
	@SuppressWarnings("unchecked")
	public INode getStalinModelOfOcurrenceNet(IOccurrenceNet<S, C> net) {
		OccurrenceNetInitialNode graphroot = new OccurrenceNetInitialNode(net);
		
		Collection<ICondition<S, C>> initialStates = net.getInitialConditions();
		Collection<IEvent<S,C>> cutOffEvents = net.getCutOffEvents();
		
		Map<ICondition<S, C>,ConditionNode> place2ConditionNode =
			new HashMap<ICondition<S, C>,ConditionNode>();
		Map<IEvent<S, C>,EventNode> transition2EventNode =
			new HashMap<IEvent<S, C>,EventNode>();

		LinkedList<Object> queue = 
			new LinkedList<Object>(initialStates);
	
		// add all initial states to model - all are successors of the graphroot
		for (ICondition<S, C> place : initialStates) {
			ConditionNode ConditionNode = new ConditionNode(place);
			place2ConditionNode.put(place,ConditionNode);
			graphroot.addOutgoingNode(ConditionNode);
			ConditionNode.addIncomingNode(graphroot);
			
		}
		
		while (!queue.isEmpty()) {
			Object node = queue.removeFirst();
			
			if (node instanceof ICondition) {
				ICondition<S,C> place = (ICondition<S,C>) node;
				ConditionNode ConditionNode = place2ConditionNode.get(place);
				for (IEvent<S, C> transition : place.getSuccessorEvents()) {
					EventNode transNode = 
						transition2EventNode.get(transition);
					if (transNode == null) {
						transNode = new EventNode(transition, cutOffEvents.contains(transition));
						transition2EventNode.put(transition, transNode);
						queue.add(transition);
					}
					ConditionNode.addOutgoingNode(transNode);
					transNode.addIncomingNode(ConditionNode);
				}
			}
			else if (node instanceof IEvent) {
				IEvent<S,C> transition = (IEvent<S,C>) node;
				EventNode EventNode = 
					transition2EventNode.get(transition);
				for (ICondition<S, C> place : transition.getSuccessorConditions()) {
					ConditionNode ConditionNode = place2ConditionNode.get(place);
					if (ConditionNode == null) {
						
						ConditionNode = new ConditionNode(place);
						place2ConditionNode.put(place, ConditionNode);
						queue.add(place);
					}
					EventNode.addOutgoingNode(ConditionNode);
					ConditionNode.addIncomingNode(EventNode);
				}
			}
		}
		return graphroot;
	}

}
