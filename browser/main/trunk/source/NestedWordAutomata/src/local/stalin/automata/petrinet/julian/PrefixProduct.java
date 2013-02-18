package local.stalin.automata.petrinet.julian;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;

import javax.naming.InitialContext;

import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.NestedWordAutomaton;
import local.stalin.automata.nwalibrary.State;
import local.stalin.automata.nwalibrary.NestedWordAutomaton.InternalTransition;
import local.stalin.automata.petrinet.IPetriNet;
import local.stalin.automata.petrinet.ITransition;
import local.stalin.automata.petrinet.Place;

public class PrefixProduct<S,C> {
	
	private final PetriNetJulian<S,C> m_Net;
	private final NestedWordAutomaton<S,C> m_Nwa;
	private PetriNetJulian<S,C> result;
	
	private HashSet<S> m_NetOnlyAlphabet;
	private HashSet<S> m_SharedAlphabet;
	private HashSet<S> m_NwaOnlyAlphabet;
	private HashSet<S> m_UnionAlphabet;
	
	private Map<Place<S,C>,Place<S,C>> oldPlace2newPlace = 
		new HashMap<Place<S,C>,Place<S,C>>();
	private Map<IState<S,C>,Place<S,C>> state2newPlace = 
		new HashMap<IState<S,C>,Place<S,C>>();
	
	private Map<S,Collection<ITransition<S,C>>> symbol2netTransitions = 
		new HashMap<S,Collection<ITransition<S,C>>>();
	private Map<S,Collection<NestedWordAutomaton<S,C>.InternalTransition>> symbol2nwaTransitions = 
		new HashMap<S,Collection<NestedWordAutomaton<S,C>.InternalTransition>>();
	
	private void updateSymbol2netTransitions(S symbol, 
											 ITransition<S,C> netTransition) {
		Collection<ITransition<S,C>> netTransitions;
		netTransitions = symbol2netTransitions.get(symbol);
		if (netTransitions == null) {
			netTransitions = new LinkedList<ITransition<S,C>>();
			symbol2netTransitions.put(symbol, netTransitions);
		}
		netTransitions.add(netTransition);
	}
	
	private void updateSymbol2nwaTransitions(S symbol, 
				NestedWordAutomaton<S,C>.InternalTransition nwaTransition) {
		Collection<NestedWordAutomaton<S,C>.InternalTransition> nwaTransitions;
		nwaTransitions = symbol2nwaTransitions.get(symbol);
		if (nwaTransitions == null) {
			nwaTransitions = new LinkedList<NestedWordAutomaton<S,C>.InternalTransition>();
			symbol2nwaTransitions.put(symbol, nwaTransitions);
		}
		nwaTransitions.add(nwaTransition);
	}
	

	
	public PrefixProduct(PetriNetJulian<S, C> net, NestedWordAutomaton<S, C> nwa) {
		this.m_Net = net;
		this.m_Nwa = nwa;
		if (nwa.getInitialStates().size() != 1) {
			throw new UnsupportedOperationException("PrefixProduct needs an" +
					" automaton with exactly one inital state");
		}
		computeResult();
	}
	
	public IPetriNet<S,C> getResult() {
		return this.result;
	}
	
	
	private void computeResult() {
		m_NetOnlyAlphabet = new HashSet<S>(m_Net.getAlphabet());
		m_NetOnlyAlphabet.removeAll(m_Nwa.getInternalAlphabet());
		m_SharedAlphabet = new HashSet<S>(m_Net.getAlphabet());
		m_SharedAlphabet.removeAll(m_NetOnlyAlphabet);
		m_NwaOnlyAlphabet = new HashSet<S>(m_Nwa.getInternalAlphabet());
		m_NwaOnlyAlphabet.removeAll(m_SharedAlphabet);
		m_UnionAlphabet = new HashSet<S>(m_Net.getAlphabet());
		m_UnionAlphabet.addAll(m_NwaOnlyAlphabet);

		// prefix product preserves the constantTokenAmount invariant
		final boolean constantTokenAmount = m_Net.constantTokenAmount();
		result = new PetriNetJulian<S,C>(m_UnionAlphabet, 
										 m_Net.getContentFactory(),
										 constantTokenAmount);
		
		//add places of old net
		for (Place<S,C> oldPlace : m_Net.getPlaces()) {
			C content = oldPlace.getContent();
			boolean isInitial = m_Net.getInitialMarking().contains(oldPlace);
			boolean isAccepting = m_Net.getAcceptingPlaces().contains(oldPlace);
			Place<S,C> newPlace = result.addPlace(content, isInitial, isAccepting);
			oldPlace2newPlace.put(oldPlace, newPlace);
		}
		
		//add states of automaton
		for (IState<S,C> state : m_Nwa.getAllStates()) {
			C content = state.getContent();
			boolean isInitial = m_Nwa.getInitialStates().contains(state);
			boolean isAccepting = m_Nwa.getFinalStates().contains(state);
			Place<S,C> newPlace = result.addPlace(content, isInitial, isAccepting);
			state2newPlace.put(state, newPlace);
		}
		
		for (ITransition<S,C> trans : m_Net.getTransitions()) {
			updateSymbol2netTransitions(trans.getSymbol(), trans);
		}
		
		for (NestedWordAutomaton<S,C>.InternalTransition trans : m_Nwa.getInternalTransitions()) {
			updateSymbol2nwaTransitions(trans.getSymbol(), trans);
		}
		
		for (S symbol : m_NetOnlyAlphabet) {
			for (ITransition<S,C> trans : symbol2netTransitions.get(symbol)) {
				Collection<Place<S,C>> predecessors = 
											new ArrayList<Place<S,C>>();
				for (Place<S,C> oldPlace : trans.getPredecessors()) {
					Place<S,C> newPlace = oldPlace2newPlace.get(oldPlace);
					predecessors.add(newPlace);
				}
				Collection<Place<S,C>> successors = 
					new ArrayList<Place<S,C>>();
				for (Place<S,C> oldPlace : trans.getSuccessors()) {
					Place<S,C> newPlace = oldPlace2newPlace.get(oldPlace);
					successors.add(newPlace);
				}
				result.addTransition(trans.getSymbol(), predecessors, successors);
			}
		}
		
		for (S symbol : m_NwaOnlyAlphabet) {
			for (NestedWordAutomaton<S,C>.InternalTransition trans : 
											symbol2nwaTransitions.get(symbol)) {
				Collection<Place<S,C>> predecessors = 
											new ArrayList<Place<S,C>>(1);
				{
					Place<S,C> newPlace = 
						state2newPlace.get(trans.getPredecessor());
					predecessors.add(newPlace);
				}
				
				Collection<Place<S,C>> successors = 
											new ArrayList<Place<S,C>>(1);
				{
					Place<S,C> newPlace = 
						state2newPlace.get(trans.getSuccessor());
					successors.add(newPlace);
				}
				result.addTransition(trans.getSymbol(), predecessors, successors);
			}
		}
		
		for (S symbol : m_SharedAlphabet) {
			if (symbol2netTransitions.containsKey(symbol))
			for (ITransition<S,C> netTrans : symbol2netTransitions.get(symbol)) {
				if (symbol2nwaTransitions.containsKey(symbol))		
				for (NestedWordAutomaton<S,C>.InternalTransition nwaTrans : 
											symbol2nwaTransitions.get(symbol)) {
				
				Collection<Place<S,C>> predecessors = 
											new ArrayList<Place<S,C>>();
				for (Place<S,C> oldPlace : netTrans.getPredecessors()) {
					Place<S,C> newPlace = oldPlace2newPlace.get(oldPlace);
					predecessors.add(newPlace);
				}
				predecessors.add(state2newPlace.get(nwaTrans.getPredecessor()));
				
				
				Collection<Place<S,C>> successors = 
					new ArrayList<Place<S,C>>();
				for (Place<S,C> oldPlace : netTrans.getSuccessors()) {
					Place<S,C> newPlace = oldPlace2newPlace.get(oldPlace);
					successors.add(newPlace);
				}
				successors.add(state2newPlace.get(nwaTrans.getSuccessor()));
				result.addTransition(netTrans.getSymbol(), predecessors, successors);
				
				}
			}
		}
		
		
		
		
		
	}

	
	
}
