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
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetAndAutomataInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.IsEquivalent;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
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

	private final Collection<PLACE> mPlaces = new HashSet<>();
	private final Set<PLACE> mInitialPlaces = new HashSet<>();
	private final Collection<PLACE> mAcceptingPlaces = new HashSet<>();
	private final Collection<ITransition<LETTER, PLACE>> mTransitions = new HashSet<>();
	/**
	 * Map each place to its incoming transitions. Redundant to {@link #mTransitions} for better performance.
	 */
	private final HashRelation<PLACE, ITransition<LETTER, PLACE>> mPredecessors = new HashRelation<>();
	/**
	 * Map each place to its outgoing transitions. Redundant to {@link #mTransitions} for better performance.
	 */
	private final HashRelation<PLACE, ITransition<LETTER, PLACE>> mSuccessors = new HashRelation<>();

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
	public BoundedPetriNet(final AutomataLibraryServices services, final INestedWordAutomaton<LETTER, PLACE> nwa) {
		this(services, nwa.getVpAlphabet().getInternalAlphabet(), true);
		final Map<PLACE, PLACE> state2place = new HashMap<>();
		for (final PLACE nwaState : nwa.getStates()) {
			final boolean isInitial = nwa.isInitial(nwaState);
			final boolean isAccepting = nwa.isFinal(nwaState);
			final PLACE place = addPlace(nwaState, isInitial, isAccepting);
			state2place.put(nwaState, place);
		}
		Set<PLACE> succPlace;
		Set<PLACE> predPlace;
		for (final PLACE content : nwa.getStates()) {
			predPlace = new HashSet<>();
			predPlace.add(state2place.get(content));
			for (final OutgoingInternalTransition<LETTER, PLACE> trans : nwa.internalSuccessors(content)) {
				succPlace = new HashSet<>();
				succPlace.add(state2place.get(trans.getSucc()));
				addTransition(trans.getLetter(), predPlace, succPlace);
			}
		}
		assert constantTokenAmountGuaranteed();
	}

	@Override
	public Set<PLACE> getSuccessors(final ITransition<LETTER, PLACE> transition) {
		return cast(transition).getSuccessors();
	}

	@Override
	public Set<PLACE> getPredecessors(final ITransition<LETTER, PLACE> transition) {
		return cast(transition).getPredecessors();
	}

	private Transition<LETTER, PLACE> cast(final ITransition<LETTER, PLACE> transition) {
		if (transition instanceof Transition) {
			return ((Transition<LETTER, PLACE>) transition);
		}
		throw new IllegalArgumentException(
				this.getClass().getSimpleName() + " works only with " + Transition.class.getSimpleName());
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

	public boolean checkResult(final INestedWordAutomaton<LETTER, PLACE> nwa,
			final IPetriNetAndAutomataInclusionStateFactory<PLACE> stateFactory) throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Testing correctness of constructor" + getClass().getSimpleName());
		}

		final boolean correct = new IsEquivalent<LETTER, PLACE>(mServices, stateFactory, this,
				nwa).getResult();
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
	 * @return the newly added place
	 */
	@SuppressWarnings("squid:S2301")
	public PLACE addPlace(final PLACE place, final boolean isInitial, final boolean isAccepting) {
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

	private void checkContentUniqueness(final PLACE content) {
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
	public Transition<LETTER, PLACE> addTransition(final LETTER letter, final Set<PLACE> preds,
			final Set<PLACE> succs) {
		assert mAlphabet.contains(letter) : "Letter not in alphabet: " + letter;
		final Transition<LETTER, PLACE> transition = new Transition<>(letter, preds, succs, mTransitions.size());
		for (final PLACE predPlace : preds) {
			assert mPlaces.contains(predPlace) : "Place not in net: " + predPlace;
			mSuccessors.addPair(predPlace, transition);
		}
		for (final PLACE succPlace : succs) {
			assert mPlaces.contains(succPlace) : "Place not in net: " + succPlace;
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
	public boolean isTransitionEnabled(final ITransition<LETTER, PLACE> transition, final Collection<PLACE> marking) {
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
	private Collection<PLACE> fireTransition(final ITransition<LETTER, PLACE> transition,
			final Collection<PLACE> marking) {
		marking.removeAll(getPredecessors(transition));
		marking.addAll(getSuccessors(transition));

		return marking;
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mAlphabet;
	}

	@Override
	public Collection<PLACE> getPlaces() {
		return mPlaces;
	}

	@Override
	public Set<PLACE> getInitialPlaces() {
		return mInitialPlaces;
	}

	@Override
	public Collection<PLACE> getAcceptingPlaces() {
		return mAcceptingPlaces;
	}

	@Override
	public Collection<ITransition<LETTER, PLACE>> getTransitions() {
		return mTransitions;
	}

	/** @return Outgoing transitions of given place. */
	@Override
	public Set<ITransition<LETTER, PLACE>> getSuccessors(final PLACE place) {
		return mSuccessors.getImage(place);
	}

	/** @return Incoming transitions of given place. */
	@Override
	public Set<ITransition<LETTER, PLACE>> getPredecessors(final PLACE place) {
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
	public boolean isAccepting(final Marking<LETTER, PLACE> marking) {
		for (final PLACE place : marking) {
			if (getAcceptingPlaces().contains(place)) {
				return true;
			}
		}
		return false;
	}

	boolean transitionsPreserveTokenAmount() {
		return mTransitions.parallelStream()
				.allMatch(transition -> getPredecessors(transition).size() == getSuccessors(transition).size());
	}

	@Override
	public int size() {
		return mPlaces.size();
	}

	@Override
	public String sizeInformation() {
		return "has " + mPlaces.size() + "places, " + mTransitions.size() + " transitions";
	}

	/** @return Letters actually being used as a label of some transition in this net. */
	public Set<LETTER> usedLetters() {
		final Set<LETTER> usedLetters = new HashSet<>();
		for (final ITransition<LETTER, PLACE> trans : mTransitions) {
			usedLetters.add(trans.getSymbol());
		}
		return usedLetters;
	}

	/** @return Number of edges in this net. */
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
		return (new AutomatonDefinitionPrinter<String, String>(mServices, "net", Format.ATS, this))
				.getDefinitionAsString();
	}

}
