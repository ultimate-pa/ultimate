/*
 * Copyright (C) 2009-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.petruchio.EmptinessPetruchio;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

public class PetriNetJulian<S, C> implements IPetriNet<S, C> {
	
	private final IUltimateServiceProvider m_Services;

	@SuppressWarnings("unused")
	private static Logger s_Logger = NestedWordAutomata.getLogger();

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

	public PetriNetJulian(IUltimateServiceProvider services, Set<S> alphabet,
			StateFactory<C> stateFactory, boolean constantTokenAmount) {
		m_Services = services;
		this.alphabet = alphabet;
		this.stateFactory = stateFactory;
		this.m_ConstantTokenAmount = constantTokenAmount;
		assert (!constantTokenAmount() || transitionsPreserveTokenAmount());
	}

	public PetriNetJulian(IUltimateServiceProvider services, 
			INestedWordAutomatonOldApi<S, C> nwa)
			throws AutomataLibraryException {
		m_Services = services;
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
		assert ResultChecker.petriNetJulian(m_Services, nwa, this);
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



	public PetriNetRun<S, C> acceptingRun() throws OperationCanceledException {
		// NestedRun<S, C> test = getAcceptingNestedRun();
		// System.out.print(test);
		return (new PetriNetUnfolder<S, C>(m_Services, this, PetriNetUnfolder.order.ERV,
				false, true)).getAcceptingRun();
	}

	public NestedRun<S, C> getAcceptingNestedRun() throws OperationCanceledException {
		EmptinessPetruchio<S, C> ep = new EmptinessPetruchio<S, C>(m_Services, this);
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
