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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.IsEquivalent;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
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


	private final Collection<C> mPlaces = new HashSet<>();
	private final Set<C> mInitialPlaces = new HashSet<>();
	private final Collection<C> mAcceptingPlaces = new HashSet<>();
	private final Collection<ITransition<LETTER, C>> mTransitions = new HashSet<>();
	/**
	 * Map each place to its incoming transitions.
	 * Redundant to {@link #mTransitions} for better performance.
	 */
	private final HashRelation<C, ITransition<LETTER, C>> mPredecessors = new HashRelation<>();
	/**
	 * Map each place to its outgoing transitions.
	 * Redundant to {@link #mTransitions} for better performance.
	 */
	private final HashRelation<C, ITransition<LETTER, C>> mSuccessors = new HashRelation<>();

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
			final boolean constantTokenAmount) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mAlphabet = alphabet;
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
		this(services, nwa.getVpAlphabet().getInternalAlphabet(), true);
		final Map<C, C> state2place = new HashMap<>();
		for (final C content : nwa.getStates()) {
			// C content = state;
			final boolean isInitial = nwa.isInitial(content);
			final boolean isAccepting = nwa.isFinal(content);
			final C place = addPlace(content, isInitial, isAccepting);
			state2place.put(content, place);
		}
		Set<C> succPlace;
		Set<C> predPlace;
		for (final C content : nwa.getStates()) {
			predPlace = new HashSet<>();
			predPlace.add(state2place.get(content));
			for (final OutgoingInternalTransition<LETTER, C> trans : nwa.internalSuccessors(content)) {
				succPlace = new HashSet<>();
				succPlace.add(state2place.get(trans.getSucc()));
				addTransition(trans.getLetter(), predPlace, succPlace);
			}
		}
		assert constantTokenAmountGuaranteed();
	}


	@Override
	public Set<C> getSuccessors(final ITransition<LETTER, C> transition) {
		if (transition instanceof Transition) {
			return ((Transition) transition).getSuccessors();
		} else {
			throw new IllegalArgumentException(this.getClass().getSimpleName() + " works only with " + Transition.class.getSimpleName());
		}
	}

	@Override
	public Set<C> getPredecessors(final ITransition<LETTER, C> transition) {
		if (transition instanceof Transition) {
			return ((Transition) transition).getPredecessors();
		} else {
			throw new IllegalArgumentException(this.getClass().getSimpleName() + " works only with " + Transition.class.getSimpleName());
		}
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

	public boolean checkResult(final INestedWordAutomaton<LETTER, C> nwa,
			final IPetriNet2FiniteAutomatonStateFactory<C> stateFactoryNet2automaton,
			final INwaInclusionStateFactory<C> stateFactoryInclusion) throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Testing correctness of constructor" + getClass().getSimpleName());
		}

		final boolean correct = new IsEquivalent<LETTER, C>(mServices, stateFactoryNet2automaton, stateFactoryInclusion,
				this, nwa).getResult();
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
	public C addPlace(final C place, final boolean isInitial, final boolean isAccepting) {
		checkContentUniqueness(place);
		mPlaces.add(place);
		if (isInitial) {
			mInitialPlaces.add(place);
		}
		if (isAccepting) {
			mAcceptingPlaces.add(place);
		}
		return place;
	}

	private void checkContentUniqueness(final C content) {
		final boolean alreadyContained = mPlaces.contains(content);
		if (alreadyContained) {
			throw new IllegalArgumentException("Must not add the same place twice: " + content);
		}
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
			final Set<C> preds, final Set<C> succs) {
		assert mAlphabet.contains(letter) : "Letter not from alphabet: " + letter;
		final Transition<LETTER, C> transition = new Transition<>(letter, preds, succs, mTransitions.size());
		for (final C predPlace : preds) {
			assert mPlaces.contains(predPlace) : "Place not from net: " + predPlace;
			mSuccessors.addPair(predPlace, transition);
		}
		for (final C succPlace : succs) {
			assert mPlaces.contains(succPlace) : "Place not from net: " + succPlace;
			mPredecessors.addPair(succPlace, transition);
		}
		mTransitions.add(transition);
		return transition;
	}


	/**
	 * @param transition
	 *            A transition from this net.
	 * @param marking
	 *            marking
	 * @return {@code true} iff the transition is enabled
	 * @deprecated currently not used
	 */
	@Deprecated
	public boolean isTransitionEnabled(final ITransition<LETTER, C> transition,
			final Collection<C> marking) {
		return marking.containsAll(getSuccessors(transition));
	}

	/**
	 * Fires a transition.
	 *
	 * @param transition
	 *            transition
	 * @param marking
	 *            marking
	 * @return resulting marking
	 * @deprecated currently not used, modifies marking
	 */
	@Deprecated
	private Collection<C> fireTransition(final ITransition<LETTER, C> transition,
			final Collection<C> marking) {
		marking.removeAll(getPredecessors(transition));
		marking.addAll(getSuccessors(transition));

		return marking;
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mAlphabet;
	}

	@Override
	public Collection<C> getPlaces() {
		return mPlaces;
	}

	@Override
	public Set<C> getInitialPlaces() {
		return mInitialPlaces;
	}

	@Override
	public Collection<C> getAcceptingPlaces() {
		return mAcceptingPlaces;
	}

	@Override
	public Collection<ITransition<LETTER, C>> getTransitions() {
		return mTransitions;
	}


	/** @return Outgoing transitions of given place. */
	@Override
	public Set<ITransition<LETTER, C>> getSuccessors(final C place) {
		return mSuccessors.getImage(place);
	}

	/** @return Incoming transitions of given place. */
	@Override
	public Set<ITransition<LETTER, C>> getPredecessors(final C place) {
		return mPredecessors.getImage(place);
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
		for (final C place : marking) {
			if (getAcceptingPlaces().contains(place)) {
				return true;
			}
		}
		return false;
	}

	boolean transitionsPreserveTokenAmount() {
		return mTransitions.parallelStream().allMatch(
				transition -> getPredecessors(transition).size() == getSuccessors(transition).size());
	}

	@Override
	public int size() {
		return mPlaces.size();
	}

	@Override
	public String sizeInformation() {
		return "has " + mPlaces.size() + "places, " + mTransitions.size() + " transitions";
	}



}
