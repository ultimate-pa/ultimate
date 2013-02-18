package local.stalin.automata.petrinet.jan;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import local.stalin.automata.Activator;
import local.stalin.automata.nwalibrary.ContentFactory;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.NestedWordAutomaton;
import local.stalin.automata.petrinet.ITransition;
import local.stalin.automata.petrinet.Place;
import local.stalin.core.api.StalinServices;

import org.apache.log4j.Logger;

public class SelfloopIntersection<S,C> {
	
	private static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private final IPetriNetJan<S,C> m_Net;
	private final NestedWordAutomaton<S,C> m_Nwa;
	private final ContentFactory<C> m_ContentFactory;
	
	private final Set<S> m_NetOnlyAlphabet;
	private final Set<S> m_NwaOnlyAlphabet;
	private final Set<S> m_SharedAlphabet;
	private final Set<S> m_UnionAlphabet;
	IPetriNetJan<S,C> m_Result;
	
	private final Map<S, Set<ITransition<S, C>>> m_Symbol2Transition; 
	
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
	
	
	
	public SelfloopIntersection(IPetriNetJan<S,C> net, NestedWordAutomaton<S,C> nwa) {
		m_Net = net;
		m_Nwa = nwa;
		m_ContentFactory = net.getContentFactory();
		m_NetOnlyAlphabet = new HashSet<S>(m_Net.getAlphabet());
		m_NetOnlyAlphabet.removeAll(m_Nwa.getInternalAlphabet());
		m_SharedAlphabet = new HashSet<S>(m_Net.getAlphabet());
		m_SharedAlphabet.removeAll(m_NetOnlyAlphabet);
		m_NwaOnlyAlphabet = new HashSet<S>(m_Nwa.getInternalAlphabet());
		m_NwaOnlyAlphabet.removeAll(m_SharedAlphabet);
		m_UnionAlphabet = new HashSet<S>(m_Net.getAlphabet());
		m_UnionAlphabet.addAll(m_NwaOnlyAlphabet);
		classifySymbols();
		m_Symbol2Transition = createSymbol2TransitionMap(net);
		copyNetStatesOnly();
		addBlackAndWhitePlaces();
		addTransitions();
		setInitialMarking();
		setAcceptingMarkings();
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
	
	public Map<S,Set<ITransition<S,C>>> createSymbol2TransitionMap(
														IPetriNetJan<S,C> net) {
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
	
	
	private void copyNetStatesOnly() {
		Collection<S> netAlphabet = m_Net.getAlphabet();
		Collection<S> nwaAlphabet = m_Nwa.getInternalAlphabet();
		Set<S> newAlphabet = new HashSet<S>(netAlphabet);
		newAlphabet.addAll(nwaAlphabet);
		m_Result = new PetriNet<S,C>(newAlphabet, m_ContentFactory);
		for (Place<S,C> oldPlace : m_Net.getPlaces()) {
			Place<S,C> newPlace = m_Result.addPlace(oldPlace.getContent());
			m_OldPlace2NewPlace.put(oldPlace, newPlace);
		}
	}
	
	
	private void addBlackAndWhitePlaces() {
		for (IState<S,C> state : m_Nwa.getAllStates()) {
			C stateContent = state.getContent();
			C whiteContent = m_ContentFactory.getWhiteContent(stateContent);
			Place<S, C> whitePlace = m_Result.addPlace(whiteContent);
			m_WhitePlace.put(state,whitePlace);
			C blackContent = m_ContentFactory.getBlackContent(stateContent);
			Place<S, C> blackPlace = m_Result.addPlace(blackContent);
			m_BlackPlace.put(state,blackPlace);
		}
	}
	
	private void addTransitions() {
		for (S symbol : m_NetOnlyAlphabet) {
			for (ITransition<S,C> transition : m_Symbol2Transition.get(symbol)) {
				Transition<S,C> newTransition = 
					createCopyOfTransition(transition);
				m_Result.addTransition(newTransition);
			}
		}
		
		for (S symbol : m_SharedAlphabet) {
			for (ITransition<S,C> oldTransition : m_Symbol2Transition.get(symbol)) {
				addTransitionForSharedSymbol(oldTransition);
			}
		}
		
		for (S symbol : m_NwaOnlyAlphabet) {
			for (IState<S,C> state : m_StateChanger.get(symbol)) {
				Transition<S,C> newTransition =  new Transition<S,C>(symbol);
				IState<S,C> succ = getSuccessorState(state, symbol);
				Place<S,C> white = m_WhitePlace.get(state);
				Place<S,C> whiteSucc = m_WhitePlace.get(succ);
				Place<S,C> black = m_BlackPlace.get(state);
				Place<S,C> blackSucc = m_BlackPlace.get(succ);
				newTransition.addPredecessorPlace(white);
				newTransition.addPredecessorPlace(blackSucc);
				newTransition.addSuccessorPlace(black);
				newTransition.addSuccessorPlace(whiteSucc);
				m_Result.addTransition(newTransition);
			}
			for (IState<S,C> state : m_Selfloop.get(symbol)) {
				Transition<S,C> newTransition =  new Transition<S,C>(symbol);
				Place<S,C> white = m_WhitePlace.get(state);
				newTransition.addPredecessorPlace(white);
				newTransition.addSuccessorPlace(white);
				m_Result.addTransition(newTransition);
			}
		}
	}
	
	private void addTransitionForSharedSymbol(ITransition<S,C> oldTransition) {
		S symbol = oldTransition.getSymbol();
		for (IState<S,C> state : m_StateChanger.get(symbol)) {
			Transition<S,C> newTransition = 
				createCopyOfTransition(oldTransition);
			IState<S,C> succ = getSuccessorState(state, symbol);
			Place<S,C> white = m_WhitePlace.get(state);
			Place<S,C> whiteSucc = m_WhitePlace.get(succ);
			Place<S,C> black = m_BlackPlace.get(state);
			Place<S,C> blackSucc = m_BlackPlace.get(succ);
			newTransition.addPredecessorPlace(white);
			newTransition.addPredecessorPlace(blackSucc);
			newTransition.addSuccessorPlace(black);
			newTransition.addSuccessorPlace(whiteSucc);
			m_Result.addTransition(newTransition);
		}
		Transition<S,C> newTransition = 
			createCopyOfTransition(oldTransition);
		for (IState<S,C> state : m_Nwa.getAllStates()) {
			if(!m_Selfloop.get(symbol).contains(state)) {
				Place<S,C> black = m_BlackPlace.get(state);
				newTransition.addPredecessorPlace(black);
				newTransition.addSuccessorPlace(black);
			}
		}
		m_Result.addTransition(newTransition);
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
	

	
	private Transition<S,C> createCopyOfTransition(
												ITransition<S,C> oldTransition) {
		Transition<S,C> newTransition = 
			new Transition<S,C>(oldTransition.getSymbol());
		for (Place<S,C> oldPre : oldTransition.getPredecessors()) {
			Place<S, C> newPre = m_OldPlace2NewPlace.get(oldPre);
			newTransition.addPredecessorPlace(newPre);
		}
		for (Place<S,C> oldSucc : oldTransition.getSuccessors()) {
			Place<S, C> newSucc = m_OldPlace2NewPlace.get(oldSucc);
			newTransition.addSuccessorPlace(newSucc);
		}
		return newTransition;
	}
	
	private void setInitialMarking() {
		Collection<IState<S,C>> nwaInitialStates = m_Nwa.getInitialStates();
		if (nwaInitialStates.size() != 1) {
			throw new IllegalArgumentException(
							"Only deterministic automata supported");
		}
		Collection<Place<S,C>> oldInitialMarking = m_Net.getInitialMarking();
		HashSet<Place<S,C>> newInitialMarking = new HashSet<Place<S,C>>();
		
		for (Place<S,C> place : oldInitialMarking) {
			newInitialMarking.add(m_OldPlace2NewPlace.get(place));
		}

		for (IState<S,C> state : m_Nwa.getAllStates()) {
			if (m_Nwa.getInitialStates().contains(state)) {
				newInitialMarking.add(m_WhitePlace.get(state));
			}
			else {
				newInitialMarking.add(m_BlackPlace.get(state));
			}
		}
		m_Result.setInitialMarking(newInitialMarking);
	}

	
	
	private void setAcceptingMarkings() {
		Set<Collection<Place<S, C>>> newAcceptingMarkings = 
			new HashSet<Collection<Place<S,C>>>();
		for (Collection<Place<S,C>> oldMarking : m_Net.getAcceptingMarkings()){
			for (IState<S,C> state : m_Nwa.getAllStates()) {
				if (state.isFinal()) {
					Collection<Place<S,C>> newMarking = 
						new HashSet<Place<S,C>>();
					for (Place<S,C> place : oldMarking) {
						newMarking.add(m_OldPlace2NewPlace.get(place));
					}
					newMarking.add(m_WhitePlace.get(state));
					for (IState<S,C> blackState : m_Nwa.getAllStates()) {
						if (blackState != state) {
							newMarking.add(m_BlackPlace.get(blackState));
						}
					}
					newAcceptingMarkings.add(newMarking);
				}
			}
		}
		m_Result.setAcceptingMarkings(newAcceptingMarkings);
	}

	public IPetriNetJan<S,C> getResult() {
		assert (isPreSuccPlaceInNet(m_Result));
		assert (isPreSuccTransitionInNet(m_Result));
		return m_Result;
	}
	
	public boolean isPreSuccPlaceInNet(IPetriNetJan<S,C> net) {
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
	
	public boolean isPreSuccTransitionInNet(IPetriNetJan<S,C> net) {
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
