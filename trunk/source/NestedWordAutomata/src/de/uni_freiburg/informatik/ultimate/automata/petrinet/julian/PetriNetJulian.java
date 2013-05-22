package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.petruchio.EmptinessPetruchio;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class PetriNetJulian<S, C> implements IPetriNet<S, C> {

	@SuppressWarnings("unused")
	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);

	private final Set<S> alphabet;
	private final StateFactory<C> stateFactory;

	private final Collection<Place<S, C>> places = new HashSet<Place<S, C>>();
	private final Set<Place<S, C>> initialPlaces = new HashSet<Place<S, C>>();
	private final Collection<Place<S, C>> acceptingPlaces = new HashSet<Place<S, C>>();
	private final Collection<ITransition<S, C>> transitions = new HashSet<ITransition<S, C>>();

	/**
	 * If true the number of tokens in this petri net is constant. Formally:
	 * There is a natural number n such that every reachable marking consists of
	 * n places.
	 */
	private final boolean m_ConstantTokenAmount;

	public PetriNetJulian(Set<S> alphabet,
			StateFactory<C> stateFactory, boolean constantTokenAmount) {
		this.alphabet = alphabet;
		this.stateFactory = stateFactory;
		this.m_ConstantTokenAmount = constantTokenAmount;
		assert (!constantTokenAmount() || transitionsPreserveTokenAmount());
	}

	public PetriNetJulian(INestedWordAutomatonOldApi<S, C> nwa)
			throws AutomataLibraryException {
		alphabet = nwa.getInternalAlphabet();
		stateFactory = nwa.getStateFactory();
		this.m_ConstantTokenAmount = true;
		Map<C, Place<S, C>> state2place = new HashMap<C, Place<S, C>>();
		for (C content : nwa.getStates()) {
			// C content = state.getContent();
			boolean isInitial = nwa.isInitial(content);
			boolean isAccepting = nwa.isFinal(content);
			Place<S, C> place = this.addPlace(content, isInitial, isAccepting);
			state2place.put(content, place);
		}
		Collection<Place<S, C>> succPlace;
		Collection<Place<S, C>> predPlace;
		for (C content : nwa.getStates()) {
			predPlace = new ArrayList<Place<S, C>>(1);
			predPlace.add(state2place.get(content));
			for (S symbol : nwa.lettersInternal(content)) {
				for (C succ : nwa.succInternal(content, symbol)) {
					succPlace = new ArrayList<Place<S, C>>(1);
					succPlace.add(state2place.get(succ));
					this.addTransition(symbol, predPlace, succPlace);
				}
				// for (C pred : nwa.predInternal(content, symbol)) {
				// predPlace = new ArrayList<Place<S, C>>(1);
				// predPlace.add(state2place.get(pred));
				// }

			}

		}

		// for (NestedWordAutomaton<S, C>.InternalTransition iTrans : nwa
		// .getInternalTransitions()) {
		// predPlace = new ArrayList<Place<S, C>>(1);
		// predPlace
		// .add(state2place.get(iTrans.getPredecessor().getContent()));
		// S symbol = iTrans.getSymbol();
		// succPlace = new ArrayList<Place<S, C>>(1);
		// succPlace.add(state2place.get(iTrans.getSuccessor().getContent()));
		// this.addTransition(symbol, predPlace, succPlace);
		// }

		assert (!constantTokenAmount() || transitionsPreserveTokenAmount());
		assert ResultChecker.petriNetJulian(nwa, this);
	}

	public Place<S, C> addPlace(C content, boolean isInitial, boolean isFinal) {
		Place<S, C> place = new Place<S, C>(content);
		places.add(place);
		if (isInitial) {
			initialPlaces.add(place);
		}
		if (isFinal) {
			acceptingPlaces.add(place);
		}
		return place;
	}

	public Transition<S, C> addTransition(S symbol,
			Collection<Place<S, C>> preds, Collection<Place<S, C>> succs) {
		if (!alphabet.contains(symbol)) {
			throw new IllegalArgumentException("unknown letter: " + symbol);
		}
		Transition<S, C> transition = new Transition<S, C>(symbol, preds,
				succs, transitions.size());
		for (Place<S, C> pred : preds) {
			if (!places.contains(pred)) {
				throw new IllegalArgumentException("unknown place");
			}
			pred.addSuccessor(transition);
		}
		for (Place<S, C> succ : succs) {
			if (!places.contains(succ)) {
				throw new IllegalArgumentException("unknown place");
			}
			succ.addPredecessor(transition);
		}
		transitions.add(transition);
		return transition;
	}

	/**
	 * Hack to satisfy requirements from IPetriNet. Used by visualization
	 */
	@Override
	public Collection<Collection<Place<S, C>>> getAcceptingMarkings() {
		ArrayList<Collection<Place<S, C>>> list = new ArrayList<Collection<Place<S, C>>>();
		list.add(acceptingPlaces);
		return list;
	}

	// public Collection<ITransition<S, C>> getEnabledTransitions(
	// Collection<Place<S, C>> marking) {
	// return CollectionExtension.from(transitions).filter(
	// new IPredicate<ITransition<S, C>>() {
	// @Override
	// public boolean test(ITransition<S, C> t) {
	// return false;
	// }
	// });
	// }

	public boolean isTransitionEnabled(ITransition<S, C> transition,
			Collection<Place<S, C>> marking) {
		return marking.containsAll(transition.getPredecessors());
	}

	public Collection<Place<S, C>> fireTransition(ITransition<S, C> transition,
			Collection<Place<S, C>> marking) {

		marking.removeAll(transition.getPredecessors());
		marking.addAll(transition.getSuccessors());

		return marking;
	}

	public Set<S> getAlphabet() {
		return alphabet;
	}

	@Override
	public StateFactory<C> getStateFactory() {
		return stateFactory;
	}

	public Collection<Place<S, C>> getPlaces() {
		return places;
	}

	public Marking<S, C> getInitialMarking() {
		return new Marking<S, C>(initialPlaces);
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
	public boolean isAccepting(Marking<S, C> marking) {
		for (Place<S, C> place : marking) {
			if (getAcceptingPlaces().contains(place)) {
				return true;
			}
		}
		return false;
	}



	/**
	 * Uses the acceptance check based on translation to finite automata
	 * 
	 * @param nw
	 * @return
	 */
	@Deprecated
	public boolean acceptsFA(Word<S> word) {
		NestedWord<S> nw = new NestedWord<S>(word);
		return (new PetriNet2FiniteAutomaton<S, C>(this)).getResult().accepts(
				nw);

	}


	public PetriNetRun<S, C> acceptingRun() throws OperationCanceledException {
		// NestedRun<S, C> test = getAcceptingNestedRun();
		// System.out.print(test);
		return (new PetriNetUnfolder<S, C>(this, PetriNetUnfolder.order.ERV,
				false, true)).getAcceptingRun();
	}

	public NestedRun<S, C> getAcceptingNestedRun() throws OperationCanceledException {
		EmptinessPetruchio<S, C> ep = new EmptinessPetruchio<S, C>(this);
		NestedRun<S, C> result = ep.getResult();

		// NestedRun<S,C> result = (new
		// PetriNet2FiniteAutomaton<S,C>(this)).getResult().
		// getAcceptingNestedRun();
		return result;
	}

	boolean transitionsPreserveTokenAmount() {
		for (ITransition<S, C> t : this.getTransitions()) {
			if (t.getPredecessors().size() != t.getSuccessors().size()) {
				return false;
			}
		}
		return true;
	}

	public int size() {
		return places.size();
	}

	public String sizeInformation() {
		return "has " + places.size() + "places, " + transitions.size()
				+ " transitions";
	}

	@Override
	public boolean accepts(Word<S> word) {
		throw new UnsupportedOperationException();
	}
}
