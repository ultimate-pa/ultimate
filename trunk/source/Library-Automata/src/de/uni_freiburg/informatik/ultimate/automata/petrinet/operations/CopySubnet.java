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
import de.uni_freiburg.informatik.ultimate.util.datastructures.SetOperations;

/**
 * Copy a Petri net N partially, creating a sub-net N'.
 * <p>
 * Given a Petri net N and a subset T' ⊆ T of its transitions,
 * create a Petri net N' with transitions T' only and places as required.
 * A place p is NOT required in N' iff N' without p still accepts L(N').
 * <p>
 * For a faster operation, some places that are not required may still be in N',
 * see {@link #requiredPlaces()}.
 * 
 * @author schaetzc@tf.uni-freiburg.de
 *
 * @param <LETTER>
 *            Type of letters in alphabet of Petri net
 * @param <PLACE>
 *            Type of places in Petri net
 */
public class CopySubnet<LETTER, PLACE> {

	private final IPetriNet<LETTER, PLACE> mOperand;
	private final Set<ITransition<LETTER, PLACE>> mTransitionSubset;
	private final BoundedPetriNet<LETTER, PLACE> mResult;

	/**
	 * Copy a net partially, creating a sub-net.
	 * 
	 * @param services services for logging and so on
	 * @param operand Petri net N to be copied partially
	 * @param transitionSubset Subset of transitions of net N forming the transitions of sub-net N'
	 */
	public CopySubnet(final AutomataLibraryServices services, final IPetriNet<LETTER, PLACE> operand,
			final Set<ITransition<LETTER, PLACE>> transitionSubset) {
		mOperand = operand;
		mTransitionSubset = transitionSubset;

		final boolean constantTokenAmount = false;
		mResult = new BoundedPetriNet<>(services, operand.getAlphabet(), constantTokenAmount);
		copySubnet();
	}

	/**
	 * Returns the result of this operation, see documentation of {@link CopySubnet}.
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

	private void rebuildPlace(PLACE place) {
		final boolean isInitial = mOperand.getInitialPlaces().contains(place);
		final boolean isAccepting = mOperand.getAcceptingPlaces().contains(place);
		mResult.addPlace(place, isInitial, isAccepting);
	}

	private void rebuildTransition(ITransition<LETTER, PLACE> trans) {
		final Set<PLACE> succ = SetOperations.intersection(mOperand.getSuccessors(trans), mResult.getPlaces());
		mResult.addTransition(trans.getSymbol(), mOperand.getPredecessors(trans), succ);
	}
	
	/**
	 * Returns a superset of the required places in a sub-net N' of a Petri net N.
	 * Sub-net N' has the same places as N, but only some transitions.
	 * <p>
	 * A place p is NOT required in N' iff N' without p still accepts L(N').
	 * <p>
	 * Even places connected to required transitions can be NOT required.
	 * When building a new net from the returned places, make sure to restrict the
	 * predecessors and successors of each transition to the new set places.
	 * 
	 * @param net Petri net N
	 * @param transitionSubset transitions of N'
	 * @return superset of the required places in N'
	 * 
	 * @return Superset of the required places
	 */
	private Set<PLACE> requiredPlaces() {
		final Set<PLACE> requiredPlaces = new HashSet<>();
		for (final ITransition<LETTER, PLACE> trans : mTransitionSubset) {
			requiredPlaces.addAll(mOperand.getPredecessors(trans));
			// successor places are only required
			// if they are predecessors of another reachable transition
			// or if they are accepting
		}
		acceptingSuccPlaces().forEach(requiredPlaces::add);
		alwaysAcceptingPlaces().findAny().ifPresent(requiredPlaces::add);
		return requiredPlaces;
	}
	
	/**
	 * Returns all accepting places that are also a successor of at least one transition
	 * from a given set of transition.
	 * 
	 * @return Successor places of T' that are also accepting
	 */
	private Stream<PLACE> acceptingSuccPlaces() {
		return mOperand.getAcceptingPlaces().stream().filter(
				accPlace -> SetOperations.intersecting(mOperand.getPredecessors(accPlace), mTransitionSubset));
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
		return acceptingInitialPlaces(mOperand).filter(
				accIniPlace -> SetOperations.disjoint(mOperand.getSuccessors(accIniPlace), mTransitionSubset));
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
