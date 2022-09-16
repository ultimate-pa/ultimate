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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetAndAutomataInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.TransitionUnifier;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.IsEquivalent;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Models 1-bounded petri nets with accepting places. Boundedness is only assumed, not checked!
 * <p>
 * A petri net is n-bounded iff at all times each place has at most n tokens. A petri net with accepting places accepts
 * a marking m iff m contains at least one accepting place.
 *
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 *            Type of letters from the alphabet used to label transitions
 * @param <PLACE>
 *            place content type
 */
public final class BoundedPetriNet<LETTER, PLACE> implements IPetriNet<LETTER, PLACE> {
	private final AutomataLibraryServices mServices;

	private final ILogger mLogger;

	private final Set<LETTER> mAlphabet;

	private final Set<PLACE> mPlaces = new HashSet<>();
	private final Set<PLACE> mInitialPlaces = new HashSet<>();
	private final Set<PLACE> mAcceptingPlaces = new HashSet<>();
	private final Set<Transition<LETTER, PLACE>> mTransitions = new HashSet<>();
	private final Set<Integer> mTransitionIds = new HashSet<>();
	private final TransitionUnifier<LETTER, PLACE> mTransitionUnifier = new TransitionUnifier<>();
	/**
	 * Map each place to its incoming transitions. Redundant to {@link #mTransitions} for better performance.
	 */
	private final HashRelation<PLACE, Transition<LETTER, PLACE>> mPredecessors = new HashRelation<>();
	/**
	 * Map each place to its outgoing transitions. Redundant to {@link #mTransitions} for better performance.
	 */
	private final HashRelation<PLACE, Transition<LETTER, PLACE>> mSuccessors = new HashRelation<>();

	/**
	 * If true the number of tokens in this petri net is constant. Formally: There is a natural number n such that every
	 * reachable marking consists of n places.
	 */
	private final boolean mConstantTokenAmount;

	private int mSizeOfFlowRelation;

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
	public BoundedPetriNet(final AutomataLibraryServices services, final INestedWordAutomaton<LETTER, PLACE> nwa) {
		this(services, nwa.getVpAlphabet().getInternalAlphabet(), true);
		final Map<PLACE, PLACE> state2place = new HashMap<>();
		for (final PLACE nwaState : nwa.getStates()) {
			final boolean isInitial = nwa.isInitial(nwaState);
			final boolean isAccepting = nwa.isFinal(nwaState);
			final boolean newlyAdded = addPlace(nwaState, isInitial, isAccepting);
			if (!newlyAdded) {
				throw new AssertionError("Automaton must not contain state twice: " + nwaState);
			}
			state2place.put(nwaState, nwaState);
		}
		for (final PLACE content : nwa.getStates()) {
			final ImmutableSet<PLACE> predPlace = ImmutableSet.singleton(state2place.get(content));
			for (final OutgoingInternalTransition<LETTER, PLACE> trans : nwa.internalSuccessors(content)) {
				final ImmutableSet<PLACE> succPlace = ImmutableSet.singleton(state2place.get(trans.getSucc()));
				addTransition(trans.getLetter(), predPlace, succPlace);
			}
		}
		assert constantTokenAmountGuaranteed();
	}

	/**
	 * If {@link #mConstantTokenAmount} is set, check that amount of tokens is preserved for all initial markings* and
	 * all firing sequences.
	 * <p>
	 * * Depending on the initial marking and reachability of some transitions, this method may return false even though
	 * {@link #mConstantTokenAmount} was set correctly to true.
	 *
	 * @return {@link #mConstantTokenAmount} implies all (not only the reachable) transitions preserve the token amount.
	 */
	private boolean constantTokenAmountGuaranteed() {
		return !constantTokenAmount() || transitionsPreserveTokenAmount();
	}

	private boolean transitionsPreserveTokenAmount() {
		return mTransitions.parallelStream()
				.allMatch(transition -> transition.getPredecessors().size() == transition.getSuccessors().size());
	}

	public boolean checkResult(final INestedWordAutomaton<LETTER, PLACE> nwa,
			final IPetriNetAndAutomataInclusionStateFactory<PLACE> stateFactory) throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Testing correctness of constructor" + getClass().getSimpleName());
		}

		final boolean correct = new IsEquivalent<>(mServices, stateFactory, this, nwa).getResult();
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of constructor " + getClass().getSimpleName());
		}
		return correct;
	}

	/**
	 * Adds a place.
	 *
	 * @param place
	 *            place to be added
	 * @param isInitial
	 *            {@code true} iff the place is initial
	 * @param isAccepting
	 *            {@code true} iff the place is final
	 * @return true iff the place was not already contained
	 */
	public boolean addPlace(final PLACE place, final boolean isInitial, final boolean isAccepting) {
		final boolean addedForFirstTime = mPlaces.add(place);
		if (addedForFirstTime) {
			if (isInitial) {
				mInitialPlaces.add(place);
			}
			if (isAccepting) {
				mAcceptingPlaces.add(place);
			}
		} else {
			if (mInitialPlaces.contains(place) != isInitial) {
				throw new IllegalArgumentException(
						"Place " + place + " was already added with different isInitial status");
			}
			if (mAcceptingPlaces.contains(place) != isAccepting) {
				throw new IllegalArgumentException(
						"Place " + place + " was already added with different isAccepting status");
			}
		}
		return addedForFirstTime;
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
	public Transition<LETTER, PLACE> addTransition(final LETTER letter, final ImmutableSet<PLACE> preds,
			final ImmutableSet<PLACE> succs, final int transitionId) {
		assert mAlphabet.contains(letter) : "Letter not in alphabet: " + letter;
		if (mTransitionIds.contains(transitionId)) {
			throw new IllegalArgumentException("Transition with id " + transitionId + " was already added.");
		}
		final Transition<LETTER, PLACE> transition = new Transition<>(letter, preds, succs, transitionId);
		final Transition<LETTER, PLACE> existingTransition = mTransitionUnifier.findOrRegister(transition);
		if (existingTransition != null) {
			return existingTransition;
		}

		for (final PLACE predPlace : preds) {
			assert mPlaces.contains(predPlace) : "Place not in net: " + predPlace;
			mSuccessors.addPair(predPlace, transition);
		}
		for (final PLACE succPlace : succs) {
			assert mPlaces.contains(succPlace) : "Place not in net: " + succPlace;
			mPredecessors.addPair(succPlace, transition);
		}
		mTransitions.add(transition);
		mTransitionIds.add(transition.getTotalOrderId());
		mSizeOfFlowRelation += (preds.size() + succs.size());
		return transition;

	}

	public Transition<LETTER, PLACE> addTransition(final LETTER letter, final ImmutableSet<PLACE> preds,
			final ImmutableSet<PLACE> succs) {
		return addTransition(letter, preds, succs, mTransitions.size());
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mAlphabet;
	}

	@Override
	public Set<PLACE> getPlaces() {
		return mPlaces;
	}

	@Override
	public Set<PLACE> getInitialPlaces() {
		return mInitialPlaces;
	}

	@Override
	public Set<PLACE> getAcceptingPlaces() {
		return mAcceptingPlaces;
	}

	@Override
	public Set<Transition<LETTER, PLACE>> getTransitions() {
		return mTransitions;
	}

	/** @return Outgoing transitions of given place. */
	@Override
	public Set<Transition<LETTER, PLACE>> getSuccessors(final PLACE place) {
		return mSuccessors.getImage(place);
	}

	/** @return Incoming transitions of given place. */
	@Override
	public Set<Transition<LETTER, PLACE>> getPredecessors(final PLACE place) {
		return mPredecessors.getImage(place);
	}

	/**
	 * @return {@code true} if the number of tokens in the net is constant (= size of initial marking) during every run
	 *         of the net.
	 */
	public boolean constantTokenAmount() {
		return mConstantTokenAmount;
	}

	@Override
	public boolean isAccepting(final Marking<PLACE> marking) {
		for (final PLACE place : marking) {
			if (getAcceptingPlaces().contains(place)) {
				return true;
			}
		}
		return false;
	}

	@Override
	public int size() {
		return mSizeOfFlowRelation;
	}

	@Override
	public String sizeInformation() {
		return "has " + mPlaces.size() + " places, " + mTransitions.size() + " transitions, " + mSizeOfFlowRelation
				+ " flow";
	}

	/** @return Number of edges in this net. */
	@Override
	public int flowSize() {
		return mPredecessors.size() + mSuccessors.size();
	}

	@Override
	public boolean isAccepting(final PLACE place) {
		if (!mPlaces.contains(place)) {
			throw new IllegalArgumentException("unknown place " + place);
		}
		return mAcceptingPlaces.contains(place);
	}

	@Override
	public String toString() {
		return AutomatonDefinitionPrinter.toString(mServices, "net", this);
	}

}
