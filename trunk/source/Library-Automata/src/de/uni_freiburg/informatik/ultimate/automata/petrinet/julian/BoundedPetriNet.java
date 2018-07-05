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
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.petruchio.EmptinessPetruchio;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.SetOperations;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Models 1-bounded petri nets with accepting places.
 * Boundedness is only assumed, not checked!
 * <p>
 * A petri net is n-bounded iff at all times each place has at most n tokens.
 * A petri net with accepting places accepts a marking m iff m contains at least one accepting place.
 * 
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * 
 * @param <LETTER>
 *            Type of letters from the alphabet used to label transitions
 * @param <C>
 *            place content type
 */
public final class BoundedPetriNet<LETTER, C> implements IPetriNet<LETTER, C> {
	private final AutomataLibraryServices mServices;

	private final ILogger mLogger;

	private final Set<LETTER> mAlphabet;
	private final IStateFactory<C> mStateFactory;

	private final Collection<Place<C>> mPlaces = new HashSet<>();
	private final Set<Place<C>> mInitialPlaces = new HashSet<>();
	private final Collection<Place<C>> mAcceptingPlaces = new HashSet<>();
	private final Collection<ITransition<LETTER, C>> mTransitions = new HashSet<>();
	/**
	 * Map each place to its incoming transitions.
	 * Redundant to {@link #mTransitions} for better performance.
	 */
	private final HashRelation<Place<C>, ITransition<LETTER, C>> mPredecessors = new HashRelation<>();
	/**
	 * Map each place to its outgoing transitions.
	 * Redundant to {@link #mTransitions} for better performance.
	 */
	private final HashRelation<Place<C>, ITransition<LETTER, C>> mSuccessors = new HashRelation<>();
	
	/**
	 * If true the number of tokens in this petri net is constant. Formally: There is a natural number n such that every
	 * reachable marking consists of n places.
	 */
	private final boolean mConstantTokenAmount;

	/**
	 * Standard constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param alphabet
	 *            Alphabet of this net, used to label transitions
	 * @param constantTokenAmount
	 *            Number of tokens in this net is constant (does not change after any firing sequence)
	 */
	public BoundedPetriNet(final AutomataLibraryServices services, final Set<LETTER> alphabet,
			final IStateFactory<C> stateFactory, final boolean constantTokenAmount) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mAlphabet = alphabet;
		mStateFactory = stateFactory;
		mConstantTokenAmount = constantTokenAmount;
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
	public BoundedPetriNet(final AutomataLibraryServices services, final INestedWordAutomaton<LETTER, C> nwa)
			throws AutomataLibraryException {
		this(services, nwa.getVpAlphabet().getInternalAlphabet(), nwa.getStateFactory(), true);
		final Map<C, Place<C>> state2place = new HashMap<>();
		for (final C content : nwa.getStates()) {
			// C content = state.getContent();
			final boolean isInitial = nwa.isInitial(content);
			final boolean isAccepting = nwa.isFinal(content);
			final Place<C> place = addPlace(content, isInitial, isAccepting);
			state2place.put(content, place);
		}
		Collection<Place<C>> succPlace;
		Collection<Place<C>> predPlace;
		for (final C content : nwa.getStates()) {
			predPlace = new ArrayList<>(1);
			predPlace.add(state2place.get(content));
			for (final OutgoingInternalTransition<LETTER, C> trans : nwa.internalSuccessors(content)) {
				succPlace = new ArrayList<>(1);
				succPlace.add(state2place.get(trans.getSucc()));
				addTransition(trans.getLetter(), predPlace, succPlace);
			}
		}
		assert constantTokenAmountGuaranteed();
		assert checkResult(nwa);
	}
	
	/**
	 * If {@link #mConstantTokenAmount} is set, check that amount of tokens is preserved for all initial markings*
	 * and all firing sequences. 
	 * <p>
	 * * Depending on the initial marking and reachability of some transitions, this method may return false
	 * even though {@link #mConstantTokenAmount} was set correctly to true.
	 * 
	 * @return {@link #mConstantTokenAmount} implies all (not only the reachable) transitions preserve the token amount.
	 */
	private boolean constantTokenAmountGuaranteed() {
		return !constantTokenAmount() || transitionsPreserveTokenAmount();
	}

	private boolean checkResult(final INestedWordAutomaton<LETTER, C> nwa) throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Testing correctness of constructor" + getClass().getSimpleName());
		}

		// TODO Christian 2017-02-15 Casts are temporary workarounds, either get a state factory or drop this check
		final INestedWordAutomaton<LETTER, C> resultAutomaton = (new PetriNet2FiniteAutomaton<>(mServices,
				(IPetriNet2FiniteAutomatonStateFactory<C>) nwa.getStateFactory(), this)).getResult();
		final boolean correct =
				new IsEquivalent<>(mServices, (INwaInclusionStateFactory<C>) getStateFactory(), resultAutomaton, nwa)
						.getResult();

		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of constructor " + getClass().getSimpleName());
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
	 * @param isAccepting
	 *            {@code true} iff the place is final
	 * @return the newly added place
	 */
	@SuppressWarnings("squid:S2301")
	public Place<C> addPlace(final C content, final boolean isInitial, final boolean isAccepting) {
		final Place<C> place = new Place<>(content);
		mPlaces.add(place);
		if (isInitial) {
			mInitialPlaces.add(place);
		}
		if (isAccepting) {
			mAcceptingPlaces.add(place);
		}
		return place;
	}

	/**
	 * Adds a transition.
	 * 
	 * @param letter
	 *            symbol
	 * @param preds
	 *            predecessor places
	 * @param succs
	 *            successor places
	 * @return the newly added transition
	 */
	public Transition<LETTER, C> addTransition(final LETTER letter,
			final Collection<Place<C>> preds, final Collection<Place<C>> succs) {
		assert mAlphabet.contains(letter) : "Letter not from alphabet: " + letter;
		final Transition<LETTER, C> transition = new Transition<>(letter, preds, succs, mTransitions.size());
		for (final Place<C> predPlace : preds) {
			assert mPlaces.contains(predPlace) : "Place not from net: " + predPlace;
			mSuccessors.addPair(predPlace, transition);
		}
		for (final Place<C> succPlace : succs) {
			assert mPlaces.contains(succPlace) : "Place not from net: " + succPlace;
			mPredecessors.addPair(succPlace, transition);
		}
		mTransitions.add(transition);
		return transition;
	}

	/**
	 * Hack to satisfy requirements from IPetriNet. Used by visualization.
	 */
	@Override
	public Collection<Collection<Place<C>>> getAcceptingMarkings() {
		final Collection<Collection<Place<C>>> list = new ArrayList<>(1);
		list.add(mAcceptingPlaces);
		return list;
	}

	/**
	 * @param transition
	 *            A transition from this net.
	 * @param marking
	 *            marking
	 * @return {@code true} iff the transition is enabled
	 */
	public boolean isTransitionEnabled(final ITransition<LETTER, C> transition,
			final Collection<Place<C>> marking) {
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
	public Collection<Place<C>> fireTransition(final ITransition<LETTER, C> transition,
			final Collection<Place<C>> marking) {
		marking.removeAll(transition.getPredecessors());
		marking.addAll(transition.getSuccessors());

		return marking;
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mAlphabet;
	}

	@Override
	public IStateFactory<C> getStateFactory() {
		return mStateFactory;
	}

	@Override
	public Collection<Place<C>> getPlaces() {
		return mPlaces;
	}

	@Override
	public Marking<LETTER, C> getInitialMarking() {
		return new Marking<>(mInitialPlaces);
	}
	
	public Set<Place<C>> getInitialPlaces() {
		return mInitialPlaces;
	}

	public Collection<Place<C>> getAcceptingPlaces() {
		return mAcceptingPlaces;
	}

	@Override
	public Collection<ITransition<LETTER, C>> getTransitions() {
		return mTransitions;
	}

	@Override
	public HashRelation<Place<C>, ITransition<LETTER, C>> getPredecessors() {
		return mPredecessors;
	}

	@Override
	public HashRelation<Place<C>, ITransition<LETTER, C>> getSuccessors() {
		return mSuccessors;
	}

	/**
	 * @return {@code true} if the number of tokens in the net is constant (= size of initial marking)
	 *         during every run of the net.
	 */
	public boolean constantTokenAmount() {
		return mConstantTokenAmount;
	}

	@Override
	public boolean isAccepting(final Marking<LETTER, C> marking) {
		for (final Place<C> place : marking) {
			if (getAcceptingPlaces().contains(place)) {
				return true;
			}
		}
		return false;
	}

	/** @return An accepting nested run. */
	public NestedRun<LETTER, C> getAcceptingNestedRun() {
		final EmptinessPetruchio<LETTER, C> ep = new EmptinessPetruchio<>(mServices, this);
		return ep.getResult();
	}

	boolean transitionsPreserveTokenAmount() {
		return mTransitions.parallelStream().allMatch(
				transition -> transition.getPredecessors().size() == transition.getSuccessors().size());
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
	public boolean accepts(final Word<LETTER> word) {
		throw new UnsupportedOperationException();
	}
	
	/**  @return This petri net accepts the empty word. */
	@Override
	public boolean acceptsEmptyWord() {
		return SetOperations.intersecting(mInitialPlaces, mAcceptingPlaces);
	}
}
