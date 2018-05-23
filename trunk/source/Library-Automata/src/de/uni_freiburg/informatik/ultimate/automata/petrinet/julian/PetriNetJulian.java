/*
 * Copyright (C) 2011-2015 Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEquivalent;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.petruchio.EmptinessPetruchio;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * A Petri net implementation.
 * 
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <S>
 *            symbol type
 * @param <C>
 *            place content type
 */
public final class PetriNetJulian<S, C> implements IPetriNet<S, C> {
	private final AutomataLibraryServices mServices;

	private final ILogger mLogger;

	private final Set<S> mAlphabet;
	private final IStateFactory<C> mStateFactory;

	private final Collection<Place<S, C>> mPlaces = new HashSet<>();
	private final Set<Place<S, C>> mInitialPlaces = new HashSet<>();
	private final Collection<Place<S, C>> mAcceptingPlaces = new HashSet<>();
	private final Collection<ITransition<S, C>> mTransitions = new HashSet<>();

	/**
	 * If true the number of tokens in this petri net is constant. Formally: There is a natural number n such that every
	 * reachable marking consists of n places.
	 */
	private final boolean mConstantTokenAmount;

	/**
	 * Private constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param alphabet
	 *            alphabet
	 * @param stateFactory
	 *            state factory
	 * @param constantTokenAmount
	 *            amount of constant tokens
	 * @param dummy
	 *            dummy parameter to avoid duplicate method signature
	 */
	@SuppressWarnings({ "unused", "squid:S1172" })
	private PetriNetJulian(final AutomataLibraryServices services, final Set<S> alphabet,
			final IStateFactory<C> stateFactory, final boolean constantTokenAmount, final boolean dummy) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mAlphabet = alphabet;
		mStateFactory = stateFactory;
		mConstantTokenAmount = constantTokenAmount;
	}

	/**
	 * Standard constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param alphabet
	 *            alphabet
	 * @param stateFactory
	 *            state factory
	 * @param constantTokenAmount
	 *            amount of constant tokens
	 */
	public PetriNetJulian(final AutomataLibraryServices services, final Set<S> alphabet,
			final IStateFactory<C> stateFactory, final boolean constantTokenAmount) {
		this(services, alphabet, stateFactory, constantTokenAmount, true);
		assert !constantTokenAmount() || transitionsPreserveTokenAmount();
	}

	/**
	 * Constructor from a nested word automaton.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param nwa
	 *            nested word automaton
	 * @throws AutomataLibraryException
	 *             if inclusion check in assertion fails
	 */
	public PetriNetJulian(final AutomataLibraryServices services, final INestedWordAutomaton<S, C> nwa)
			throws AutomataLibraryException {
		this(services, nwa.getVpAlphabet().getInternalAlphabet(), nwa.getStateFactory(), true, false);
		final Map<C, Place<S, C>> state2place = new HashMap<>();
		for (final C content : nwa.getStates()) {
			// C content = state.getContent();
			final boolean isInitial = nwa.isInitial(content);
			final boolean isAccepting = nwa.isFinal(content);
			final Place<S, C> place = addPlace(content, isInitial, isAccepting);
			state2place.put(content, place);
		}
		Collection<Place<S, C>> succPlace;
		Collection<Place<S, C>> predPlace;
		for (final C content : nwa.getStates()) {
			predPlace = new ArrayList<>(1);
			predPlace.add(state2place.get(content));
			for (final OutgoingInternalTransition<S, C> trans : nwa.internalSuccessors(content)) {
				succPlace = new ArrayList<>(1);
				succPlace.add(state2place.get(trans.getSucc()));
				addTransition(trans.getLetter(), predPlace, succPlace);
			}
		}

		/*
		for (NestedWordAutomaton<S, C>.InternalTransition iTrans : nwa.getInternalTransitions()) {
			predPlace = new ArrayList<Place<S, C>>(1);
			predPlace.add(state2place.get(iTrans.getPredecessor().getContent()));
			S symbol = iTrans.getSymbol();
			succPlace = new ArrayList<Place<S, C>>(1);
			succPlace.add(state2place.get(iTrans.getSuccessor().getContent()));
			addTransition(symbol, predPlace, succPlace);
		}
		*/

		assert !constantTokenAmount() || transitionsPreserveTokenAmount();
		assert checkResult(nwa);
	}

	private boolean checkResult(final INestedWordAutomaton<S, C> nwa) throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Testing correctness of PetriNetJulian constructor");
		}

		// TODO Christian 2017-02-15 Casts are temporary workarounds, either get a state factory or drop this check
		final INestedWordAutomaton<S, C> resultAutomaton = (new PetriNet2FiniteAutomaton<>(mServices,
				(IPetriNet2FiniteAutomatonStateFactory<C>) nwa.getStateFactory(), this)).getResult();
		final boolean correct =
				new IsEquivalent<>(mServices, (INwaInclusionStateFactory<C>) getStateFactory(), resultAutomaton, nwa)
						.getResult();

		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of PetriNetJulian constructor");
		}
		return correct;
	}

	/**
	 * Adds a place.
	 * 
	 * @param content
	 *            content
	 * @param isInitial
	 *            {@code true} iff the place is initial
	 * @param isFinal
	 *            {@code true} iff the place is final
	 * @return the newly added place
	 */
	@SuppressWarnings("squid:S2301")
	public Place<S, C> addPlace(final C content, final boolean isInitial, final boolean isFinal) {
		final Place<S, C> place = new Place<>(content);
		mPlaces.add(place);
		if (isInitial) {
			mInitialPlaces.add(place);
		}
		if (isFinal) {
			mAcceptingPlaces.add(place);
		}
		return place;
	}

	/**
	 * Adds a transition.
	 * 
	 * @param symbol
	 *            symbol
	 * @param preds
	 *            predecessor places
	 * @param succs
	 *            successor places
	 * @return the newly added transition
	 */
	public Transition<S, C> addTransition(final S symbol, final Collection<Place<S, C>> preds,
			final Collection<Place<S, C>> succs) {
		if (!mAlphabet.contains(symbol)) {
			throw new IllegalArgumentException("unknown letter: " + symbol);
		}
		final Transition<S, C> transition = new Transition<>(symbol, preds, succs, mTransitions.size());
		for (final Place<S, C> pred : preds) {
			if (!mPlaces.contains(pred)) {
				throw new IllegalArgumentException("unknown place");
			}
			pred.addSuccessor(transition);
		}
		for (final Place<S, C> succ : succs) {
			if (!mPlaces.contains(succ)) {
				throw new IllegalArgumentException("unknown place");
			}
			succ.addPredecessor(transition);
		}
		mTransitions.add(transition);
		return transition;
	}

	/**
	 * Hack to satisfy requirements from IPetriNet. Used by visualization.
	 */
	@Override
	public Collection<Collection<Place<S, C>>> getAcceptingMarkings() {
		final Collection<Collection<Place<S, C>>> list = new ArrayList<>(1);
		list.add(mAcceptingPlaces);
		return list;
	}

	/*
	public Collection<ITransition<S, C>> getEnabledTransitions(Collection<Place<S, C>> marking) {
		return CollectionExtension.from(transitions).filter(new IPredicate<ITransition<S, C>>() {
			@Override
			public boolean test(ITransition<S, C> t) {
				return false;
			}
		});
	}
	*/

	/**
	 * @param transition
	 *            A transition.
	 * @param marking
	 *            marking
	 * @return {@code true} iff the transition is enabled
	 */
	public boolean isTransitionEnabled(final ITransition<S, C> transition, final Collection<Place<S, C>> marking) {
		return marking.containsAll(transition.getPredecessors());
	}

	/**
	 * Fires a transition.
	 * 
	 * @param transition
	 *            transition
	 * @param marking
	 *            marking
	 * @return resulting marking
	 */
	public Collection<Place<S, C>> fireTransition(final ITransition<S, C> transition,
			final Collection<Place<S, C>> marking) {
		marking.removeAll(transition.getPredecessors());
		marking.addAll(transition.getSuccessors());

		return marking;
	}

	@Override
	public Set<S> getAlphabet() {
		return mAlphabet;
	}

	@Override
	public IStateFactory<C> getStateFactory() {
		return mStateFactory;
	}

	@Override
	public Collection<Place<S, C>> getPlaces() {
		return mPlaces;
	}

	@Override
	public Marking<S, C> getInitialMarking() {
		return new Marking<>(mInitialPlaces);
	}

	public Collection<Place<S, C>> getAcceptingPlaces() {
		return mAcceptingPlaces;
	}

	@Override
	public Collection<ITransition<S, C>> getTransitions() {
		return mTransitions;
	}

	/**
	 * @return {@code true} if the number of tokens in the net is constant (= size of initial marking) during every run
	 *         of the net.
	 */
	public boolean constantTokenAmount() {
		return mConstantTokenAmount;
	}

	@Override
	public boolean isAccepting(final Marking<S, C> marking) {
		for (final Place<S, C> place : marking) {
			if (getAcceptingPlaces().contains(place)) {
				return true;
			}
		}
		return false;
	}


	/**
	 * @return An accepting nested run.
	 */
	public NestedRun<S, C> getAcceptingNestedRun() {
		final EmptinessPetruchio<S, C> ep = new EmptinessPetruchio<>(mServices, this);
		// NestedRun<S,C> result = (new PetriNet2FiniteAutomaton<S,C>(this)).getResult().getAcceptingNestedRun();
		return ep.getResult();
	}

	boolean transitionsPreserveTokenAmount() {
		for (final ITransition<S, C> t : getTransitions()) {
			if (t.getPredecessors().size() != t.getSuccessors().size()) {
				return false;
			}
		}
		return true;
	}

	@Override
	public int size() {
		return mPlaces.size();
	}

	@Override
	public String sizeInformation() {
		return "has " + mPlaces.size() + "places, " + mTransitions.size() + " transitions";
	}

	@Override
	public boolean accepts(final Word<S> word) {
		throw new UnsupportedOperationException();
	}
}
