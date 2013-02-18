package local.stalin.automata.petrinet.julian;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import local.stalin.automata.Activator;
import local.stalin.automata.nwalibrary.ContentFactory;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.NestedWordAutomaton;
import local.stalin.automata.nwalibrary.NestedWordAutomaton.InternalTransition;
import local.stalin.automata.nwalibrary.NestedWordAutomaton.InternalTransitions;
import local.stalin.automata.petrinet.ITransition;
import local.stalin.automata.petrinet.Place;
import local.stalin.core.api.StalinServices;

import org.apache.log4j.Logger;

public class DifferenceBlackAndWhite<S,C> {
	
	private static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private final PetriNetJulian<S,C> m_Net;
	private final NestedWordAutomaton<S,C> m_Nwa;
	private final ContentFactory<C> m_ContentFactory;
	
	PetriNetJulian<S,C> m_Result;
	
	private final Map<S, Set<NestedWordAutomaton<S,C>.InternalTransition>> m_Symbol2AutomatonTransition;
	
	private final Map<Place<S,C>,Place<S,C>> m_OldPlace2NewPlace =
		new HashMap<Place<S,C>,Place<S,C>>();
	
	private final Map<S,Set<IState<S,C>>> m_Selfloop = 
		new HashMap<S,Set<IState<S,C>>>();
	private final Map<S,Set<IState<S,C>>> m_StateChanger = 
		new HashMap<S,Set<IState<S,C>>>();
	
	private final Map<IState<S,C>,Place<S,C>> m_WhitePlace =
		new HashMap<IState<S,C>,Place<S,C>>();
	
	private final Map<IState<S,C>,Place<S,C>> m_BlackPlace =
		new HashMap<IState<S,C>,Place<S,C>>();
	
	
	
	public DifferenceBlackAndWhite(PetriNetJulian<S,C> net, NestedWordAutomaton<S,C> nwa) {
		m_Net = net;
		m_Nwa = nwa;
		m_ContentFactory = net.getContentFactory();
		Collection<S> netAlphabet = new HashSet<S>(net.getAlphabet());
		Collection<S> nwaAlpahbet = new HashSet<S>(nwa.getInternalAlphabet());
		if (!netAlphabet.equals(nwaAlpahbet)) {
			throw new IllegalArgumentException("net and nwa must use same" +
					" alphabet");
		}
		if (nwa.getInitialStates().size() != 1) {
			throw new UnsupportedOperationException("DifferenceBlackAndWhite" +
					" needs an automaton with exactly one inital state");
		}
		classifySymbols();
		m_Symbol2AutomatonTransition = createSymbol2AutomatonTransitionMap();
		copyNet_StatesOnly();
		addBlackAndWhitePlaces();
		addTransitions();
	}
	
	
	
	private void classifySymbols() {
		for (S symbol : m_Nwa.getInternalAlphabet()) {
			HashSet<IState<S, C>> selfloopStates = new HashSet<IState<S,C>>();
			HashSet<IState<S, C>> changerStates = new HashSet<IState<S,C>>();
			for (IState<S,C> state : m_Nwa.getAllStates()) {
				Collection<IState<S,C>> successors = 
					state.getInternalSucc(symbol);
				if (successors.isEmpty()) {
					continue;
				}
				if (successors.size() > 1) {
					throw new IllegalArgumentException(
									"Only deterministic automata supported");
				}
				if (successors.contains(state)) {
					selfloopStates.add(state);
				}
				else {
					changerStates.add(state);
				}
			}
			m_Selfloop.put(symbol,selfloopStates);
			m_StateChanger.put(symbol, changerStates);
			s_Logger.debug(symbol + " " + selfloopStates.size() + 
				" times selfloop " + changerStates.size() + " times changer");
		}
	}
	
	public Map<S,Set<NestedWordAutomaton<S,C>.InternalTransition>> createSymbol2AutomatonTransitionMap() {
		Map<S,Set<NestedWordAutomaton<S,C>.InternalTransition>> result = 
			new HashMap<S,Set<NestedWordAutomaton<S,C>.InternalTransition>>();
		for (NestedWordAutomaton<S,C>.InternalTransition trans : m_Nwa.getInternalTransitions()) {
			S symbol = trans.getSymbol();
			Set<NestedWordAutomaton<S,C>.InternalTransition> transitions = 
				result.get(symbol);
			if (transitions == null) {
				transitions = new HashSet<NestedWordAutomaton<S,C>.InternalTransition>();
				result.put(symbol,transitions);
			}
			transitions.add(trans);
		}
		return result;
	}
	
	
	public Map<S,Set<ITransition<S,C>>> createSymbol2TransitionMap(
														PetriNetJulian<S,C> net) {
		Map<S,Set<ITransition<S,C>>> result = 
			new HashMap<S,Set<ITransition<S,C>>>();
		for (S symbol : net.getAlphabet()) {
			result.put(symbol, new HashSet<ITransition<S,C>>());
		}
		for (ITransition<S,C> transition : net.getTransitions()) {
			result.get(transition.getSymbol()).add(transition);
		}
		return result;	
	}
	
	
	private void copyNet_StatesOnly() {
		
		// difference black and white preserves the constantTokenAmount invariant
		final boolean constantTokenAmount = m_Net.constantTokenAmount();
		m_Result = new PetriNetJulian<S,C>(m_Net.getAlphabet(),
											m_Net.getContentFactory(),
											constantTokenAmount);
		
		for (Place<S,C> oldPlace : m_Net.getPlaces()) {
			C content = oldPlace.getContent();
			boolean isInitial = m_Net.getInitialMarking().contains(oldPlace);
			boolean isAccepting = m_Net.getAcceptingPlaces().contains(oldPlace);
			Place<S,C> newPlace = m_Result.addPlace(content, isInitial, isAccepting);
			m_OldPlace2NewPlace.put(oldPlace, newPlace);
		}
		
	}
	
	
	private void addBlackAndWhitePlaces() {
		for (IState<S,C> state : m_Nwa.getAllStates()) {
			if (!m_Nwa.isFinal(state)) {
				boolean isInitial = m_Nwa.getInitialStates().contains(state);
				C stateContent = state.getContent();
				C whiteContent = m_ContentFactory.getWhiteContent(stateContent);
				Place<S,C> whitePlace = m_Result.addPlace(whiteContent,isInitial,false);
				m_WhitePlace.put(state,whitePlace);
				C blackContent = m_ContentFactory.getBlackContent(stateContent);
				Place<S,C> blackPlace = m_Result.addPlace(blackContent,!isInitial,false);
				m_BlackPlace.put(state,blackPlace);
			}
		}
	}
	
	private void addTransitions() {
		for (ITransition<S, C> oldTrans : m_Net.getTransitions()) {
			S symbol = oldTrans.getSymbol();
			
			// A copy for each changer
			for (IState<S,C> predState : m_StateChanger.get(symbol)) {
				Collection<IState<S,C>> succStates = predState.getInternalSucc(symbol);
				assert (succStates.size() == 1);
				IState<S,C> succState = succStates.iterator().next();	
				
				// omit transitions to final states
				if (m_Nwa.isFinal(succState)) {
					continue;
				}
				
				Collection<Place<S,C>> predecessors = 
					new ArrayList<Place<S,C>>();
				for (Place<S,C> oldPlace : oldTrans.getPredecessors()) {
					Place<S,C> newPlace = m_OldPlace2NewPlace.get(oldPlace);
					predecessors.add(newPlace);
				}
				assert(m_WhitePlace.containsKey(predState));
				predecessors.add(m_WhitePlace.get(predState));
				assert(m_WhitePlace.containsKey(succState));
				predecessors.add(m_BlackPlace.get(succState));
				
				Collection<Place<S,C>> successors = 
					new ArrayList<Place<S,C>>();
				for (Place<S,C> oldPlace : oldTrans.getSuccessors()) {
					Place<S,C> newPlace = m_OldPlace2NewPlace.get(oldPlace);
					successors.add(newPlace);
				}
				assert(m_WhitePlace.containsKey(succState));
				successors.add(m_WhitePlace.get(succState));
				assert(m_BlackPlace.containsKey(predState));
				successors.add(m_BlackPlace.get(predState));
				
				m_Result.addTransition(oldTrans.getSymbol(), predecessors, successors);
			}
			
			// One copy for the selfloops
			if (!m_Selfloop.isEmpty()) {
//				Collection<IState<S,C>> succStates = predState.getInternalSucc(symbol);
//				assert (succStates.size() == 1);
//				IState<S,C> succState = succStates.iterator().next();				
				Collection<Place<S,C>> predecessors = 
					new ArrayList<Place<S,C>>();
				for (Place<S,C> oldPlace : oldTrans.getPredecessors()) {
					Place<S,C> newPlace = m_OldPlace2NewPlace.get(oldPlace);
					predecessors.add(newPlace);
				}
//				predecessors.add(m_WhitePlace.get(predState));
//				predecessors.add(m_BlackPlace.get(succState));
				
				Collection<Place<S,C>> successors = 
					new ArrayList<Place<S,C>>();
				for (Place<S,C> oldPlace : oldTrans.getSuccessors()) {
					Place<S,C> newPlace = m_OldPlace2NewPlace.get(oldPlace);
					successors.add(newPlace);
				}
//				successors.add(m_WhitePlace.get(succState));
//				successors.add(m_BlackPlace.get(predState));
				
				for (IState<S,C> state : m_StateChanger.get(symbol)) {
					predecessors.add(m_BlackPlace.get(state));
					successors.add(m_BlackPlace.get(state));
				}
				
				m_Result.addTransition(oldTrans.getSymbol(), predecessors, successors);
			}
		}
	}
		
		
	
		

	
	private IState<S,C> getSuccessorState(IState<S,C> state, S symbol) {
		Collection<IState<S, C>> successors = state.getInternalSucc(symbol);
		if (successors.size() > 1) {
			throw new IllegalArgumentException(
							"Only deterministic automata supported");
		}
		for (IState<S,C> succ : successors) {
			return succ;
		}
		return null;
	}
	

	
	
	

	public PetriNetJulian<S,C> getResult() {
		assert (isPreSuccPlaceInNet(m_Result));
		assert (isPreSuccTransitionInNet(m_Result));
		return m_Result;
	}
	
	public boolean isPreSuccPlaceInNet(PetriNetJulian<S,C> net) {
		for (ITransition<S,C> trans : net.getTransitions()) {
			for (Place<S,C> place : trans.getPredecessors()) {
				if(!net.getPlaces().contains(place)) {
					return false;
				}
			}
			for (Place<S,C> place : trans.getSuccessors()) {
				if(!net.getPlaces().contains(place)) {
					return false;
				}
			}
		}
		return true;
	}
	
	public boolean isPreSuccTransitionInNet(PetriNetJulian<S,C> net) {
		for (Place<S,C> place : net.getPlaces()) {
			for (ITransition<S,C> trans : place.getPredecessors()) {
				if(!net.getTransitions().contains(trans)) {
					return false;
				}
			}
			for (ITransition<S,C> trans : place.getSuccessors()) {
				if(!net.getTransitions().contains(trans)) {
					return false;
				}
			}
		}
		return true;
	}

}
