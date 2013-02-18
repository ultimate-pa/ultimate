package de.uni_freiburg.informatik.ultimate.automata.petrinet;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;


/**
 * Given a PetriNet, constructs a finite Automaton that recognizes the same
 * language.
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <S> Symbol
 * @param <C> Content
 */
public class PetriNet2FiniteAutomaton<S,C> {
	
	private final IPetriNet<S, C> m_Net;
	private final NestedWordAutomaton<S,C> m_Result;
	
	/**
	 * List of markings for which
	 * <ul>
	 * <li> there has already been a state constructed
	 * <li> outgoing transitions of this state have not yet been constructed.
	 * </ul>
 
	 */
	private final List<Marking<S,C>> m_Worklist = 
		new LinkedList<Marking<S,C>>();
	/**
	 * Maps a marking to the automaton state that represents this marking.
	 */
	Map<Marking<S,C>,C> m_Marking2State =
		new HashMap<Marking<S,C>,C>();
	StateFactory<C> m_ContentFactory;


	
	
	/**
	 * Returns the automaton state that represents marking. If this state is not
	 * yet constructed, construct it and enqueue the marking. If it has to be
	 * constructed it is an initial state iff isInitial is true. 
	 */
	private C getState(Marking<S,C> marking, boolean isInitial) {
		C state = m_Marking2State.get(marking);
		if (state == null) {
//			boolean isFinal = m_Net.getAcceptingMarkings().contains(marking);
			boolean isFinal = m_Net.isAccepting(marking);
			state = m_ContentFactory.getContentOnPetriNet2FiniteAutomaton(marking);
			m_Result.addState(isInitial, isFinal, state);
			m_Marking2State.put(marking,state);
			m_Worklist.add(marking);
		}
		return state;
	}
	
	private Collection<C> getMarkingContents(Set<Place<S,C>> marking) {
		ArrayList<C> result = new ArrayList<C>(marking.size());
		for (Place<S,C> place : marking) {
			result.add(place.getContent());
		}
		return result;
	}

	
	
	/**
	 * Given a marking. Get the state that represents the marking. Add all
	 * possible outgoing automaton transitions to state. Construct (and
	 * enqueue to worklist) successor states if necessary.
	 */
	private void constructOutgoingTransitions(Marking<S,C> marking) {
		C state = getState(marking, false);
		Set<ITransition<S,C>> outgoing = getOutgoingNetTransitions(marking);
		for (ITransition<S,C> transition : outgoing) {
			if (marking.isTransitionEnabled(transition)) {
				Marking<S,C> succMarking = marking.fireTransition(transition);
				C succState = getState(succMarking, false);
				m_Result.addInternalTransition(state, transition.getSymbol(),
																	succState);
				
			}
		}
		
	}
	
//	
//	private boolean isEnabled(ITransition<S,C> transition, 
//													Set<Place<S,C>> marking) {
//		if (marking.containsAll(transition.getPredecessors())) {
//			return true;
//		}
//		else return false;
//	}
	
	
	private Set<ITransition<S, C>> getOutgoingNetTransitions(
													Marking<S,C> marking) {
		Set<ITransition<S,C>> transitions = new HashSet<ITransition<S,C>>();
		for (Place<S,C> place : marking) {
			transitions.addAll(place.getSuccessors());
		}
		return transitions;
	}

	
	
	public PetriNet2FiniteAutomaton(IPetriNet<S,C> net) {
		m_Net = net;
		m_ContentFactory = net.getStateFactory();
		Set<S> alphabet = new HashSet<S>(net.getAlphabet());
		m_Result = new NestedWordAutomaton<S,C>(alphabet,
									 new HashSet<S>(0),
									 new HashSet<S>(0),
									 net.getStateFactory());
		getState(net.getInitialMarking(),true);
		while (!m_Worklist.isEmpty()) {
			Marking<S,C> marking = m_Worklist.remove(0);
			constructOutgoingTransitions(marking);
		}
	}
	
	public NestedWordAutomaton<S,C> getResult() {
		return m_Result;
	}
	
	
	

}
