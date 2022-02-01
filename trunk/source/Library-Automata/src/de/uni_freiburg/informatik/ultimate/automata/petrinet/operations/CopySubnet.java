/*
 * Copyright (C) 2018 schaetzc@tf.uni-freiburg.de
 * Copyright (C) 2009-2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.SetOperations;

/**
 * Copies a Petri net N partially, creating a sub-net N'.
 * <p>
 * Given a Petri net N and a subset T' ⊆ T of its transitions,
 * creates a Petri net N' with transitions T' and required places (see {@link #requiredPlaces()}) only.
 *
 * @author schaetzc@tf.uni-freiburg.de
 *
 * @param <LETTER>
 *            Type of letters in alphabet of Petri net
 * @param <PLACE>
 *            Type of places in Petri net
 */
public class CopySubnet<LETTER, PLACE> {

	/** The Petri Net for which we copy partially to create a sub-net. */
	private final IPetriNet<LETTER, PLACE> mSuperNet;
	private final boolean mKeepSuccessorPlaces;
	private final Set<ITransition<LETTER, PLACE>> mTransitionSubset;
	private final BoundedPetriNet<LETTER, PLACE> mResult;

	/**
	 * Copies a net partially, creating a sub-net. The sub-net is defined in terms
	 * of transitions. Places that are no longer required are excluded
	 * automatically.
	 *
	 * @param <LETTER>
	 *            Type of the transition labels in the old and new petri net
	 * @param <PLACE>
	 *            Type of the places in the old and new petri net
	 * @param services
	 *            Services for logging and so on
	 * @param superNet
	 *            Petri net N to be copied partially
	 * @param transitionSubset
	 *            Subset of transitions of net N forming the transitions of sub-net
	 *            N'
	 * @param newAlphabet
	 *            New alphabet of sub-net N'. The new alphabet can be a subset or
	 *            superset of the old alphabet, however, all labels from
	 *            {@code transitionSubset} have to be included.
	 * @param keepSuccessorPlaces
	 *            Whether or not to keep successor places for all included
	 *            transitions. Setting this to false may result in transitions with
	 *            an empty post-set.
	 * @return Subnet N'
	 */
	public static <LETTER, PLACE> BoundedPetriNet<LETTER, PLACE> copy(final AutomataLibraryServices services,
			final IPetriNet<LETTER, PLACE> superNet, final Set<ITransition<LETTER, PLACE>> transitionSubset,
			final Set<LETTER> newAlphabet, final boolean keepSuccessorPlaces) {
		return new CopySubnet<>(services, superNet, transitionSubset, newAlphabet, keepSuccessorPlaces).getResult();
	}

	/**
	 * Copies a net partially, creating a sub-net.
	 * The sub-net is defined in terms of transitions.
	 * Places that are no longer required are excluded automatically.
	 *
	 * @param <LETTER> Type of the transition labels in the old and new petri net
	 * @param <PLACE> Type of the places in the old and new petri net
	 * @param services Services for logging and so on
	 * @param superNet Petri net N to be copied partially
	 * @param transitionSubset Subset of transitions of net N forming the transitions of sub-net N'
	 * @param newAlphabet New alphabet of sub-net N'.
	 *                    The new alphabet can be a subset or superset of the old alphabet,
	 *                    however, all labels from {@code transitionSubset} have to be included.
	 * @return Subnet N'
	 */
	public static <LETTER, PLACE> BoundedPetriNet<LETTER, PLACE> copy(final AutomataLibraryServices services,
			final IPetriNet<LETTER, PLACE> superNet, final Set<ITransition<LETTER, PLACE>> transitionSubset,
			final Set<LETTER> newAlphabet) {
		return copy(services, superNet, transitionSubset, newAlphabet, false);
	}

	/**
	 * Copies a net partially, creating a sub-net.
	 * The sub-net is defined in terms of transitions.
	 * Places that are no longer required are excluded automatically.
	 * The alphabet stays the same, even if some letters are no longer used.
	 *
	 * @param <LETTER> Type of the transition labels in the old and new petri net
	 * @param <PLACE> Type of the places in the old and new petri net
	 * @param services Services for logging and so on
	 * @param superNet Petri net N to be copied partially
	 * @param transitionSubset Subset of transitions of net N forming the transitions of sub-net N'
	 * @return Subnet N'
	 */
	public static <LETTER, PLACE> BoundedPetriNet<LETTER, PLACE> copy(final AutomataLibraryServices services,
			final IPetriNet<LETTER, PLACE> superNet, final Set<ITransition<LETTER, PLACE>> transitionSubset) {
		return copy(services, superNet, transitionSubset, superNet.getAlphabet());
	}

	/**
	 * Copies a net partially, creating a sub-net.
	 *
	 * @param services Services for logging and so on
	 * @param superNet Petri net N to be copied partially
	 * @param transitionSubset Subset of transitions of net N forming the transitions of sub-net N'
	 * @param keepSuccessorPlaces Whether or not to keep successor places for all included transitions.
	 *   			Setting this to false may result in transitions with an empty post-set.
	 */
	private CopySubnet(final AutomataLibraryServices services, final IPetriNet<LETTER, PLACE> superNet,
			final Set<ITransition<LETTER, PLACE>> transitionSubset, final Set<LETTER> newAlphabet, final boolean keepSuccessorPlaces) {
		mSuperNet = superNet;
		mKeepSuccessorPlaces = keepSuccessorPlaces;
		mTransitionSubset = transitionSubset;

		final boolean constantTokenAmount = false;
		mResult = new BoundedPetriNet<>(services, newAlphabet, constantTokenAmount);
		copySubnet();
	}

	/**
	 * Returns the result of the operation modeled by this class,
	 * see documentation of {@link CopySubnet}.
	 *
	 * @return Sub-net
	 */
	public BoundedPetriNet<LETTER, PLACE> getResult() {
		return mResult;
	}

	private void copySubnet() {
		requiredPlaces().forEach(this::rebuildPlace);
		mTransitionSubset.forEach(this::rebuildTransition);
	}

	private void rebuildPlace(final PLACE place) {
		final boolean isInitial = mSuperNet.getInitialPlaces().contains(place);
		final boolean isAccepting = mSuperNet.getAcceptingPlaces().contains(place);
		final boolean newlyAdded = mResult.addPlace(place, isInitial, isAccepting);
		if (!newlyAdded) {
			throw new AssertionError("Must not add place twice: " + place);
		}
	}

	private void rebuildTransition(final ITransition<LETTER, PLACE> trans) {
		final Set<PLACE> succ = SetOperations.intersection(mSuperNet.getSuccessors(trans), mResult.getPlaces());
		mResult.addTransition(trans.getSymbol(), mSuperNet.getPredecessors(trans), succ);
	}

	/**
	 * Returns a the required places in a sub-net N' of a Petri net N.
	 * Sub-net N' has the same places as N, but only some transitions.
	 * <p>
	 * A place p is required in N' iff
	 * p is predecessor of some transition in N',
	 * or p is accepting and successor of some transition in N',
	 * or p is accepting and initial in N'.
	 *
	 * @param net Petri net N
	 * @param transitionSubset transitions of N'
	 * @return required places in N'
	 *
	 * @return Superset of the required places
	 */
	private Set<PLACE> requiredPlaces() {
		final Set<PLACE> requiredPlaces = new HashSet<>();
		for (final ITransition<LETTER, PLACE> trans : mTransitionSubset) {
			requiredPlaces.addAll(mSuperNet.getPredecessors(trans));

			// successor places are only really required
			// if they are predecessors of another reachable transition
			// or if they are accepting
			if (mKeepSuccessorPlaces) {
				requiredPlaces.addAll(mSuperNet.getSuccessors(trans));
			}
		}
		acceptingSuccPlaces().forEach(requiredPlaces::add);
		// one of all always accepting places would be sufficient, but not deterministic
		alwaysAcceptingPlaces().forEach(requiredPlaces::add);
		return requiredPlaces;
	}

	/**
	 * Returns all accepting places that are also a successor of at least one transition
	 * from a given set of transition.
	 *
	 * @return Successor places of T' that are also accepting
	 */
	private Stream<PLACE> acceptingSuccPlaces() {
		return mSuperNet.getAcceptingPlaces().stream().filter(accPlace -> DataStructureUtils.haveNonEmptyIntersection(
					mSuperNet.getPredecessors(accPlace), mTransitionSubset));
	}

	/**
	 * Returns all places that are accepting, initial, and not connected to any transition
	 * in a sub-net N' of a Petri net N. Sub-net N' has the same places as N, but only some transitions.
	 * <p>
	 * The returned places are only a subset of the places which are always accepting.
	 * Places that are always accepting because their outgoing transitions can never fire are not considered.
	 * Places that are always accepting because their outgoing transitions are also incoming are not considered.
	 *
	 * @return subset of the always accepting places in N'
	 */
	private Stream<PLACE> alwaysAcceptingPlaces() {
		return acceptingInitialPlaces(mSuperNet).filter(accIniPlace -> DataStructureUtils.haveEmptyIntersection(
				mSuperNet.getSuccessors(accIniPlace), mTransitionSubset));
	}

	/**
	 * Returns all places that are accepting and initial.
	 *
	 * @return accepting initial places of N
	 */
	private static <LETTER, PLACE> Stream<PLACE> acceptingInitialPlaces(final IPetriNet<LETTER, PLACE> net) {
		return net.getAcceptingPlaces().stream().filter(net.getInitialPlaces()::contains);
	}
}
