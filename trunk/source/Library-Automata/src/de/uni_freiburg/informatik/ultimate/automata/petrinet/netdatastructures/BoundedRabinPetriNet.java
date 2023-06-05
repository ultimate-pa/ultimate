package de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetAndAutomataInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public final class BoundedRabinPetriNet<LETTER, PLACE> implements IRabinPetriNet<LETTER, PLACE> {
	private final BoundedPetriNet<LETTER, PLACE> mPetriNet;
	private final Set<PLACE> mFinitePlaces = new HashSet<>();

	public BoundedRabinPetriNet(final BoundedPetriNet<LETTER, PLACE> net) {
		mPetriNet = net;
	}

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
	public BoundedRabinPetriNet(final AutomataLibraryServices services, final Set<LETTER> alphabet,
			final boolean constantTokenAmount) {
		mPetriNet = new BoundedPetriNet<>(services, alphabet, constantTokenAmount);
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
	public BoundedRabinPetriNet(final AutomataLibraryServices services, final INestedWordAutomaton<LETTER, PLACE> nwa) {
		mPetriNet = new BoundedPetriNet<>(services, nwa);
	}

	/**
	 * Adds place to finite set, place has to be added with addplace() before.
	 *
	 * @param place
	 */
	public void addFinitePlace(final PLACE place) {
		mFinitePlaces.add(place);
	}

	@Override
	public Set<PLACE> getFinitePlaces() {
		return mFinitePlaces;
	}

	@Override
	public boolean isFinite(final PLACE place) {
		return mFinitePlaces.contains(place);
	}

	public boolean checkResult(final INestedWordAutomaton<LETTER, PLACE> nwa,
			final IPetriNetAndAutomataInclusionStateFactory<PLACE> stateFactory) throws AutomataLibraryException {
		return mPetriNet.checkResult(nwa, stateFactory);
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
		return mPetriNet.addPlace(place, isInitial, isAccepting);
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
		return mPetriNet.addTransition(letter, preds, succs, transitionId);
	}

	public Transition<LETTER, PLACE> addTransition(final LETTER letter, final ImmutableSet<PLACE> preds,
			final ImmutableSet<PLACE> succs) {
		return mPetriNet.addTransition(letter, preds, succs);
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mPetriNet.getAlphabet();
	}

	@Override
	public Set<PLACE> getPlaces() {
		return mPetriNet.getPlaces();
	}

	@Override
	public Set<PLACE> getInitialPlaces() {
		return mPetriNet.getInitialPlaces();
	}

	@Override
	public Set<PLACE> getAcceptingPlaces() {
		return mPetriNet.getAcceptingPlaces();
	}

	@Override
	public Set<Transition<LETTER, PLACE>> getTransitions() {
		return mPetriNet.getTransitions();
	}

	/** @return Outgoing transitions of given place. */
	@Override
	public Set<Transition<LETTER, PLACE>> getSuccessors(final PLACE place) {
		return mPetriNet.getSuccessors(place);
	}

	/** @return Incoming transitions of given place. */
	@Override
	public Set<Transition<LETTER, PLACE>> getPredecessors(final PLACE place) {
		return mPetriNet.getPredecessors(place);
	}

	/**
	 * @return {@code true} if the number of tokens in the net is constant (= size of initial marking) during every run
	 *         of the net.
	 */
	public boolean constantTokenAmount() {
		return mPetriNet.constantTokenAmount();
	}

	@Override
	public boolean isAccepting(final Marking<PLACE> marking) {
		return mPetriNet.isAccepting(marking);
	}

	@Override
	public int size() {
		return mPetriNet.size();
	}

	@Override
	public String sizeInformation() {
		return mPetriNet.sizeInformation();
	}

	/** @return Number of edges in this net. */
	@Override
	public int flowSize() {
		return mPetriNet.flowSize();
	}

	@Override
	public boolean isAccepting(final PLACE place) {
		return mPetriNet.isAccepting(place);
	}

	@Override
	public String toString() {
		return mPetriNet.toString();
	}
}
