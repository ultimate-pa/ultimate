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
	private final NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>> mEmpireAutomaton;
	private final HashRelation<State<L, P>, Region<P>> mLegalFocus;
	private final IPetriNet<L, P> mNet;

	public LegalFocus(final NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>> empire,
			final IPetriNet<L, P> net) {
		mEmpireAutomaton = empire;
		mNet = net;
		mLegalFocus = computeLegalFocus();
	}

	private HashRelation<State<L, P>, Region<P>> computeLegalFocus() {
		final var finalStates = mEmpireAutomaton.getFinalStates().stream().collect(Collectors.toSet());
		final var queue = new ArrayDeque<State<L, P>>();
		final var focus = computeFinalStateFocus(finalStates);
		for (final State<L, P> state : finalStates) {
			queue.offer(state);
		}
		while (!queue.isEmpty()) {
			final var state = queue.poll();
			final var currentFocus = focus.getImage(state);
			if (currentFocus.isEmpty()) {
				continue;
			}
			final var predecessors = mEmpireAutomaton.internalPredecessors(state);
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
		final var focused = new HashSet<Region<P>>();
		final var territory = predecessor.territory();
		final var bystanders = territory.getBystanders(transition);
		final var focusedBystanders = DataStructureUtils.intersection(bystanders, successorFocus);
		if (successorFocus.size() == focusedBystanders.size()) {
			return focusedBystanders;
		}
		final var mayRegions = territory.getPlacesRegions(transition.getPredecessors());
		final var minRegion = mayRegions.stream().min(Comparator.comparingInt(r -> r.getPlaces().size())).orElse(null);
		if (minRegion != null) {
			focused.add(minRegion);
		}
		focused.addAll(focusedBystanders);
		return focused;
	}

	private HashRelation<State<L, P>, Region<P>> computeFinalStateFocus(final Set<State<L, P>> finalStates) {
		final var focus = new HashRelation<State<L, P>, Region<P>>();
		for (final State<L, P> state : finalStates) {
			final var territory = state.territory();
			final var enabledTransitions = territory.getEnabledTransitions(mNet);
			final var successorlessTransitions =
					enabledTransitions.filter(t -> !mEmpireAutomaton.internalSuccessors(state, t).iterator().hasNext())
							.collect(Collectors.toSet());
			for (final Transition<L, P> transition : successorlessTransitions) {
				final var mayRegions = territory.getPlacesRegions(transition.getPredecessors());
				final var minRegion =
						mayRegions.stream().min(Comparator.comparingInt(r -> r.getPlaces().size())).orElse(null);
				if (minRegion != null) {
					focus.addPair(state, minRegion);
				}

			}
		}
		return focus;
	}

}
