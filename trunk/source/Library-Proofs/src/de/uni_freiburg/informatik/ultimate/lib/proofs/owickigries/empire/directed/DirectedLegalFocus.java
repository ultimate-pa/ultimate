/*
 * Copyright (C) 2025 Matthias Zumkeller
 * Copyright (C) 2025 University of Freiburg
 *
 * This file is part of the ULTIMATE Proofs Library.
 *
 * The ULTIMATE Proofs Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Proofs Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Proofs Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Proofs Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Proofs Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.directed;

import java.util.ArrayDeque;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.Region;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.directed.DirectedEmpire.State;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class DirectedLegalFocus<L, P> {
	private final HashRelation<State<L, P>, ConnectedRegion<L, P>> mLegalFocus;
	private final IPetriNet<L, P> mNet;

	public DirectedLegalFocus(final NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>> empire,
			final IPetriNet<L, P> net) {
		mNet = net;
		mLegalFocus = computeLegalFocus(empire);
	}

	public DirectedLegalFocus(final Set<NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>>> empires,
			final IPetriNet<L, P> net) {
		mNet = net;
		mLegalFocus = computeLegalFocus(empires);
	}

	private HashRelation<State<L, P>, ConnectedRegion<L, P>>
			computeLegalFocus(final Set<NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>>> empires) {
		final var focus = new HashRelation<State<L, P>, ConnectedRegion<L, P>>();
		for (final NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>> empire : empires) {
			final var empireFocus = computeLegalFocus(empire);
			focus.addAll(empireFocus);
		}
		return focus;
	}

	private HashRelation<State<L, P>, ConnectedRegion<L, P>>
			computeLegalFocus(final NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>> empire) {
		final var finalStates = empire.getFinalStates().stream().collect(Collectors.toSet());
		final var queue = new ArrayDeque<State<L, P>>();
		final var focus = computeFinalStateFocus(empire, finalStates);
		for (final State<L, P> state : finalStates) {
			queue.offer(state);
		}
		while (!queue.isEmpty()) {
			final var state = queue.poll();
			final var currentFocus = focus.getImage(state);
			if (currentFocus.isEmpty()) {
				continue;
			}
			final var predecessors = empire.internalPredecessors(state);
			for (final IncomingInternalTransition<Transition<L, P>, State<L, P>> incomingInternalTransition : predecessors) {
				final var predecessor = incomingInternalTransition.getPred();
				final var transition = incomingInternalTransition.getLetter();
				final var focusedRegions = getFocusedRegions(predecessor, currentFocus, transition);
				final var added = focus.addAllPairs(predecessor, focusedRegions);
				if (added) {
					queue.offer(predecessor);
				}
			}
		}
		return focus;
	}

	private Set<ConnectedRegion<L, P>> getFocusedRegions(final State<L, P> predecessor,
			final Set<ConnectedRegion<L, P>> successorFocus, final Transition<L, P> transition) {
		final var territory = predecessor.territory();
		final var bystanders = territory.getBystanders(transition);
		final var focusedBystanders = DataStructureUtils.intersection(bystanders, successorFocus);
		if (successorFocus.size() == focusedBystanders.size()) {
			return focusedBystanders;
		}

		final var mayRegions = territory.getPlacesRegions(transition.getPredecessors());
		assert !mayRegions.isEmpty() : "territory enables transition but has no predecessor regions";

		// TODO Check if any regions in mayRegions are already focused; if so, choose one of those.
		final var minRegion = mayRegions.stream().min(Comparator.comparingInt(Region::size));
		assert minRegion.isPresent() : "could not find best predecessor region";

		final var focused = new HashSet<>(focusedBystanders);
		focused.add(minRegion.orElseThrow());
		return focused;
	}

	private HashRelation<State<L, P>, ConnectedRegion<L, P>> computeFinalStateFocus(
			final NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>> empire,
			final Set<State<L, P>> finalStates) {
		final var focus = new HashRelation<State<L, P>, ConnectedRegion<L, P>>();
		for (final State<L, P> state : finalStates) {
			final var territory = state.territory();
			final var enabledTransitions = territory.getEnabledTransitions(mNet);
			final var successorlessTransitions = enabledTransitions
					.filter(t -> !empire.internalSuccessors(state, t).iterator().hasNext()).collect(Collectors.toSet());
			for (final Transition<L, P> transition : successorlessTransitions) {
				final var mayRegions = territory.getPlacesRegions(transition.getPredecessors());
				assert !mayRegions.isEmpty() : "territory enables transition but has no predecessor regions";

				// TODO Check if any regions in mayRegions are already focused; if so, choose one of those.
				final var minRegion = mayRegions.stream().min(Comparator.comparingInt(Region::size));
				assert minRegion.isPresent() : "could not find best predecessor region";

				focus.addPair(state, minRegion.orElseThrow());
			}
		}
		return focus;
	}

	public Set<ConnectedRegion<L, P>> getLegalFocus(final State<L, P> state) {
		return mLegalFocus.getImage(state);
	}

	public boolean isFocused(final P place, final State<L, P> state) {
		final var legalFocus = getLegalFocus(state);
		return legalFocus.stream().anyMatch(r -> r.contains(place));
	}
}
