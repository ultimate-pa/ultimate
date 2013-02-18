package de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.Event;
import de.uni_freiburg.informatik.ultimate.model.INode;

public class BranchingProcessToUltimateModel<S, C> {
	
	
	
	@SuppressWarnings("unchecked")
	public INode getUltimateModelOfBranchingProcess(BranchingProcess<S, C> branchingProcess) {
		BranchingProcessInitialNode<S, C> graphroot = new BranchingProcessInitialNode<S, C>(branchingProcess);
		
		Collection<Condition<S, C>> initialStates = branchingProcess.initialConditions();
//		Collection<Event<S,C>> cutOffEvents = net.getCutOffEvents();
		
		Map<Condition<S, C>,ConditionNode<S,C>> place2ConditionNode =
			new HashMap<Condition<S, C>,ConditionNode<S,C>>();
		Map<Event<S, C>,EventNode<S,C>> transition2EventNode =
			new HashMap<Event<S, C>,EventNode<S,C>>();

		LinkedList<Object> queue = 
			new LinkedList<Object>(initialStates);
	
		// add all initial states to model - all are successors of the graphroot
		for (Condition<S, C> place : initialStates) {
			ConditionNode<S,C> ConditionNode = new ConditionNode<S,C>(place,branchingProcess);
			place2ConditionNode.put(place,ConditionNode);
			graphroot.addOutgoingNode(ConditionNode);
			ConditionNode.addIncomingNode(graphroot);
			
		}
		
		while (!queue.isEmpty()) {
			Object node = queue.removeFirst();
			
			if (node instanceof Condition) {
				Condition<S,C> place = (Condition<S,C>) node;
				ConditionNode<S,C> ConditionNode = place2ConditionNode.get(place);
				for (Event<S,C> transition : place.getSuccessorEvents()) {
					EventNode<S,C> transNode = 
						transition2EventNode.get(transition);
					if (transNode == null) {
						transNode = new EventNode<S,C>(transition);
						transition2EventNode.put(transition, transNode);
						queue.add(transition);
					}
					ConditionNode.addOutgoingNode(transNode);
					transNode.addIncomingNode(ConditionNode);
				}
			}
			else if (node instanceof Event) {
				Event<S,C> transition = (Event<S,C>) node;
				EventNode<S,C> EventNode = 
					transition2EventNode.get(transition);
				for (Condition<S, C> place : transition.getSuccessorConditions()) {
					ConditionNode<S,C> ConditionNode = place2ConditionNode.get(place);
					if (ConditionNode == null) {
						
						ConditionNode = new ConditionNode<S,C>(place,branchingProcess);
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
