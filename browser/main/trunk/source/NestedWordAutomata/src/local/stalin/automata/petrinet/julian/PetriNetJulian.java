package local.stalin.automata.petrinet.julian;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import local.stalin.automata.Activator;
import local.stalin.automata.NestedWordAutomata;
import local.stalin.automata.nwalibrary.ConcurrentProduct;
import local.stalin.automata.nwalibrary.ContentFactory;
import local.stalin.automata.nwalibrary.INestedWordAutomaton;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.NestedRun;
import local.stalin.automata.nwalibrary.NestedWord;
import local.stalin.automata.nwalibrary.NestedWordAutomaton;
import local.stalin.automata.nwalibrary.operations.DifferenceAutomatonBuilder;
import local.stalin.automata.petrinet.IPetriNet;
import local.stalin.automata.petrinet.ITransition;
import local.stalin.automata.petrinet.Place;
import local.stalin.automata.petrinet.jan.PetriNet2FiniteAutomaton;
import local.stalin.automata.petrinet.julian.emptinesspetruchio.EmptinessPetruchio;
import local.stalin.core.api.StalinServices;

import org.apache.log4j.Logger;

public class PetriNetJulian<S,C> implements IPetriNet<S,C>{
	
	private static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private final Collection<S> alphabet;
	private final ContentFactory<C> contentFactory;
	
	private final Collection<Place<S,C>> places =
		new HashSet<Place<S,C>>();
	private final Collection<Place<S,C>> initialPlaces =
		new HashSet<Place<S,C>>();
	private final Collection<Place<S,C>> acceptingPlaces =
		new HashSet<Place<S,C>>();
	private final Collection<ITransition<S,C>> transitions =
		new HashSet<ITransition<S,C>>();
	
	/**
	 * If true the number of tokens in this petri net is constant. Formally:
	 * There is a natural number n such that every reachable marking consists of
	 * n places.
	 */
	private final boolean m_ConstantTokenAmount;

	
	
	public PetriNetJulian(Collection<S> alphabet, 
						  ContentFactory<C> contentFactory,
						  boolean constantTokenAmount) {
		this.alphabet = alphabet;
		this.contentFactory = contentFactory;
		this.m_ConstantTokenAmount = constantTokenAmount;
		assert (!constantTokenAmount() || transitionsPreserveTokenAmount());
	}

	
	public PetriNetJulian(NestedWordAutomaton<S,C> nwa) {
		alphabet = nwa.getInternalAlphabet();
		contentFactory = nwa.getContentFactory();
		this.m_ConstantTokenAmount = true;
		Map<IState<S,C>,Place<S,C>> state2place = 
			new HashMap<IState<S,C>,Place<S,C>>();
		for (IState<S,C> state : nwa.getAllStates()) {
			C content = state.getContent();
			boolean isInitial = nwa.getInitialStates().contains(state);
			boolean isAccepting = nwa.getFinalStates().contains(state);
			Place<S,C> place = this.addPlace(content,isInitial,isAccepting);
			state2place.put(state,place);
		}
//		for (IState<S,C> state : nwa.getAllStates()) {
//			for (S symbol : alphabet) {
//				for (IState<S,C> succ : state.getInternalSucc(symbol)) {
//					Collection<Place<S,C>> predPlace = 
//												new ArrayList<Place<S,C>>(1);
//					predPlace.add(state2place.get(state));
//					Collection<Place<S,C>> succPlace = 
//												new ArrayList<Place<S,C>>(1);
//					succPlace.add(state2place.get(succ));
//					this.addTransition(symbol, predPlace, succPlace);
//				}
//			}
//		}
		
		for (NestedWordAutomaton<S,C>.InternalTransition iTrans : 
												nwa.getInternalTransitions()) {
			Collection<Place<S,C>> predPlace = 
				new ArrayList<Place<S,C>>(1);
			predPlace.add(state2place.get(iTrans.getPredecessor()));
			S symbol = iTrans.getSymbol();
			Collection<Place<S,C>> succPlace = 
				new ArrayList<Place<S,C>>(1);
			succPlace.add(state2place.get(iTrans.getSuccessor()));
			this.addTransition(symbol, predPlace, succPlace);
		}
		
		if (NestedWordAutomata.TEST) {
			NestedWordAutomaton<S,C> result2automaton = 
				(new PetriNet2FiniteAutomaton<S,C>(this)).getResult();
			assert (nwa.included(nwa, result2automaton) == null);
			assert (nwa.included(result2automaton, nwa) == null);
		}
		assert (!constantTokenAmount() || transitionsPreserveTokenAmount());
		
	}
	



	public Place<S,C> addPlace(C content, boolean isInitial, boolean isFinal) {
		Place<S,C> place = new Place<S,C>(content);
		places.add(place);
		if (isInitial) {
			initialPlaces.add(place);
		}
		if (isFinal) {
			acceptingPlaces.add(place);
		}
		return place;
	}
	
	

	public void addTransition(S symbol, 
							  Collection<Place<S,C>> preds, 
							  Collection<Place<S,C>> succs) {
		Transition<S,C> transition = new Transition<S,C>(symbol, preds, succs);
		for (Place<S,C> pred : preds) {
			if (!places.contains(pred)) {
				throw new IllegalArgumentException("unknown place");
			}
			pred.addSuccessor(transition);
		}
		for (Place<S,C> succ : succs) {
			if (!places.contains(succ)) {
				throw new IllegalArgumentException("unknown place");
			}
			succ.addPredecessor(transition);
		}
		transitions.add(transition);
	}



	/**
	 * Hack to satisfy requirements from IPetriNet. Used by visualization
	 */
	@Override
	public Collection<Collection<Place<S,C>>> getAcceptingMarkings() {
		ArrayList<Collection<Place<S,C>>> list = 
			new ArrayList<Collection<Place<S,C>>>();
		list.add(acceptingPlaces);
		return list;
	}



	public Collection<S> getAlphabet() {
		return alphabet;
	}

	public ContentFactory<C> getContentFactory() {
		return contentFactory;
	}

	public Collection<Place<S, C>> getPlaces() {
		return places;
	}

	public Collection<Place<S, C>> getInitialMarking() {
		return initialPlaces;
	}


	public Collection<Place<S, C>> getAcceptingPlaces() {
		return acceptingPlaces;
	}


	public Collection<ITransition<S, C>> getTransitions() {
		return transitions;
	}
	
	/**
	 * if true, then the number of tokens in the net is constant (= size of
	 * initial marking) during every run of the net
	 */
	public boolean constantTokenAmount() {
		return m_ConstantTokenAmount;
	}


	@Override
	public boolean isAccepting(Collection<Place<S, C>> marking) {
		for (Place<S,C> place : marking) {
			if (getAcceptingPlaces().contains(place)) {
				return true;
			}
		}
		return false;
	}


	
	public IPetriNet<S,C> prefixProduct(
						PetriNetJulian<S,C> net, NestedWordAutomaton<S,C> nwa) {
		IPetriNet<S,C> result = (new PrefixProduct<S,C>(net,nwa)).getResult();
		if (NestedWordAutomata.TEST) {
			s_Logger.debug("Testing correctness of prefixProduct");
			INestedWordAutomaton<S,C> netAsAutomaton =
				(new PetriNet2FiniteAutomaton<S,C>(net)).getResult();
			INestedWordAutomaton<S,C> prefixProductAutomaton =
				(NestedWordAutomaton<S,C>) 
				(new ConcurrentProduct<S,C>(netAsAutomaton, nwa, true)).getResult();
			INestedWordAutomaton<S,C> resultAsAutomaton =
				(new PetriNet2FiniteAutomaton<S,C>(result)).getResult();
			assert (nwa.included(resultAsAutomaton, prefixProductAutomaton) == null);
			assert (nwa.included(prefixProductAutomaton, resultAsAutomaton) == null);
		}
		return result;
	}
	
	
	public PetriNetJulian<S,C> differenceBlackAndWhite(
						PetriNetJulian<S,C> net, NestedWordAutomaton<S,C> nwa) {
		PetriNetJulian<S,C> result = 
						(new DifferenceBlackAndWhite<S,C>(net,nwa)).getResult();
		if (NestedWordAutomata.TEST) {
			s_Logger.debug("Testing correctness of differenceBlackAndWhite");
			INestedWordAutomaton<S,C> netAsAutomaton =
				(new PetriNet2FiniteAutomaton<S,C>(net)).getResult();
			INestedWordAutomaton<S,C> differenceAutomaton =
				new DifferenceAutomatonBuilder<S,C>(netAsAutomaton, nwa).getResult();
			INestedWordAutomaton<S,C> resultAsAutomaton =
				(new PetriNet2FiniteAutomaton<S,C>(result)).getResult();
			assert (nwa.included(resultAsAutomaton, differenceAutomaton) == null);
			NestedRun<S,C> counterexample = 
							nwa.included(differenceAutomaton, resultAsAutomaton);
			assert (counterexample == null);
		}
		return result;
	}
	
	
	
	
	public boolean accepts(NestedWord<S> nw) {
		return (new PetriNet2FiniteAutomaton<S,C>(this)).getResult().accepts(nw);
	}
	
	
	public NestedRun<S, C> getAcceptingNestedRun() {
		EmptinessPetruchio<S,C> ep = new EmptinessPetruchio<S,C>(this);
		NestedRun<S,C> result = ep.getResult();
		if (NestedWordAutomata.TEST) {
			s_Logger.debug("Testing correctness of EmptinessPetruchio");
			if (result == null) {
				NestedRun<S,C> automataRun = 
					(new PetriNet2FiniteAutomaton<S,C>(this)).getResult().
					getAcceptingNestedRun();
				assert(automataRun == null);
			}
		}
		else {
			assert(accepts(result.getNestedWord()));
		}
//		NestedRun<S,C> result = (new PetriNet2FiniteAutomaton<S,C>(this)).getResult().
//		getAcceptingNestedRun();
		return result;
	}
	
//	public NestedRun<S,C> getAcceptingNestedRun() {
//		return (new PetriNet2FiniteAutomaton<S,C>(this)).getResult().getAcceptingNestedRun();
//	}
	
	boolean transitionsPreserveTokenAmount() {
		for (ITransition<S,C> t : this.getTransitions()) {
			if (t.getPredecessors().size() != t.getSuccessors().size()) {
				return false;
			}
		}
		return true;
	}
	
}
