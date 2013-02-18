package local.stalin.automata.petrinet.visualization;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

import local.stalin.automata.petrinet.Place;
import local.stalin.automata.petrinet.ITransition;
import local.stalin.automata.petrinet.IPetriNet;
import local.stalin.model.INode;

public class PetriNetToStalinModel<S, C> {
	
	@SuppressWarnings("unchecked")
	public INode getStalinModelOfPetriNet(IPetriNet<S, C> net) {
		Collection<Collection<Place<S, C>>> acceptingMarkings = 
			net.getAcceptingMarkings();
		PetriNetInitialNode graphroot = 
			new PetriNetInitialNode(printAcceptingMarkings(acceptingMarkings));
		
		Collection<Place<S, C>> initialStates = net.getInitialMarking();

		
		Map<Place<S, C>,PlaceNode> place2placeNode =
			new HashMap<Place<S, C>,PlaceNode>();
		Map<ITransition<S, C>,TransitionNode> transition2transitionNode =
			new HashMap<ITransition<S, C>,TransitionNode>();

		LinkedList<Object> queue = 
			new LinkedList<Object>(initialStates);
	
		// add all initial states to model - all are successors of the graphroot
		for (Place<S, C> place : initialStates) {
			PlaceNode placeNode = new PlaceNode(place.getContent(),
					participatedAcceptingMarkings(place, acceptingMarkings));
			place2placeNode.put(place,placeNode);
			graphroot.addOutgoingNode(placeNode);
			placeNode.addIncomingNode(graphroot);
			
		}
		
		while (!queue.isEmpty()) {
			Object node = queue.removeFirst();
			
			if (node instanceof Place) {
				Place<S,C> place = (Place<S,C>) node;
				PlaceNode placeNode = place2placeNode.get(place);
				for (ITransition<S, C> transition : place.getSuccessors()) {
					TransitionNode transNode = 
						transition2transitionNode.get(transition);
					if (transNode == null) {
						transNode = new TransitionNode(transition.getSymbol());
						transition2transitionNode.put(transition, transNode);
						queue.add(transition);
					}
					placeNode.addOutgoingNode(transNode);
					transNode.addIncomingNode(placeNode);
				}
			}
			else if (node instanceof ITransition) {
				ITransition<S,C> transition = (ITransition<S,C>) node;
				TransitionNode transitionNode = 
					transition2transitionNode.get(transition);
				for (Place<S, C> place : transition.getSuccessors()) {
					PlaceNode placeNode = place2placeNode.get(place);
					if (placeNode == null) {
						
						placeNode = new PlaceNode(place.getContent(),
										participatedAcceptingMarkings(place,
															acceptingMarkings));
						place2placeNode.put(place, placeNode);
						queue.add(place);
					}
					transitionNode.addOutgoingNode(placeNode);
					placeNode.addIncomingNode(transitionNode);
				}
			}
		}
		return graphroot;
	}
	
	
	private Collection<String> participatedAcceptingMarkings(Place<S,C> place,
					Collection<Collection<Place<S, C>>> acceptingMarkings) {
		LinkedList<String> participatedAcceptingMarkings = 
													new LinkedList<String>();
		for (Collection<Place<S, C>> acceptingMarking : acceptingMarkings) {
			if (acceptingMarking.contains(place)) {
				String acceptingMarkingString = "{ ";
				for (Place<S,C> placeInMarking : acceptingMarking) {
					acceptingMarkingString += 
										placeInMarking.getContent().toString();
					acceptingMarkingString += " , ";
				}
				acceptingMarkingString = acceptingMarkingString.substring(0,
											acceptingMarkingString.length()-3);
				acceptingMarkingString += "}";
				participatedAcceptingMarkings.add(acceptingMarkingString);
			}
		}
		return participatedAcceptingMarkings;
	}
	
	private Collection<String> printAcceptingMarkings(
			Collection<Collection<Place<S, C>>> acceptingMarkings) {
		LinkedList<String> acceptingMarkingsList = new LinkedList<String>();
		for (Collection<Place<S, C>> acceptingMarking : acceptingMarkings) {
			if (acceptingMarking.isEmpty()) {
				acceptingMarkingsList.add("{ }");
			}
			else {
				String acceptingMarkingString = "{ ";
				for (Place<S,C> placeInMarking : acceptingMarking) {
					acceptingMarkingString += 
										placeInMarking.getContent().toString();
					acceptingMarkingString += " , ";
				}
				acceptingMarkingString = acceptingMarkingString.substring(0, 
											acceptingMarkingString.length()-3);
				acceptingMarkingString += "}";
				acceptingMarkingsList.add(acceptingMarkingString);
			}
		}
		return acceptingMarkingsList;
}

}
