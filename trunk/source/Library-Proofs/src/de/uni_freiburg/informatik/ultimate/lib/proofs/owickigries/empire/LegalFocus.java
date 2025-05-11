package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire;

import java.util.ArrayDeque;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireAutomaton.State;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class LegalFocus<L, P> {
	private final HashRelation<State<L, P>, Region<P>> mLegalFocus;
	private final IPetriNet<L, P> mNet;

	public LegalFocus(final NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>> empire,
			final IPetriNet<L, P> net) {
		mNet = net;
		mLegalFocus = computeLegalFocus(empire);
	}

	public LegalFocus(final Set<NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>>> empires,
			final IPetriNet<L, P> net) {
		mNet = net;
		mLegalFocus = computeLegalFocus(empires);
	}

	private HashRelation<State<L, P>, Region<P>>
			computeLegalFocus(final Set<NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>>> empires) {
		final var focus = new HashRelation<State<L, P>, Region<P>>();
		for (final NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>> empire : empires) {
			final var empireFocus = computeLegalFocus(empire);
			focus.addAll(empireFocus);
		}
		return focus;
	}

	private HashRelation<State<L, P>, Region<P>>
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

	private Set<Region<P>> getFocusedRegions(final State<L, P> predecessor, final Set<Region<P>> successorFocus,
			final Transition<L, P> transition) {
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

	private HashRelation<State<L, P>, Region<P>> computeFinalStateFocus(
			final NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>> empire,
			final Set<State<L, P>> finalStates) {
		final var focus = new HashRelation<State<L, P>, Region<P>>();
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

	public Set<Region<P>> getLegalFocus(final State<L, P> state) {
		return mLegalFocus.getImage(state);
	}

	public boolean isFocused(final P place, final State<L, P> state) {
		final var legalFocus = getLegalFocus(state);
		return legalFocus.stream().anyMatch(r -> r.contains(place));
	}
}
