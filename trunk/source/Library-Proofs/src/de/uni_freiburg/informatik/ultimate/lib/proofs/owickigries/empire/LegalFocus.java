package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.ModularEmpireAutomaton.State;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class LegalFocus<L, P> implements ILegalFocusFunction<State<L, P>, P> {
	private final HashRelation<Pair<State<L, P>, Integer>, Region<P>> mLegalFocus;
	private final IPetriNet<L, P> mNet;
	private final INwaOutgoingLetterAndTransitionProvider<L, List<IPredicate>> mProduct;
	private final int mNumLaws;

	public LegalFocus(final NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>> empire,
			final IPetriNet<L, P> net, final INwaOutgoingLetterAndTransitionProvider<L, List<IPredicate>> product,
			final int numLaws) {
		mNet = net;
		mProduct = product;
		mNumLaws = numLaws;
		mLegalFocus = computeLegalFocus(empire);
	}

	private HashRelation<Pair<State<L, P>, Integer>, Region<P>>
			computeLegalFocus(final NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>> empire) {
		final var finalStates = empire.getFinalStates().stream().collect(Collectors.toSet());
		final var queue = new ArrayDeque<State<L, P>>();
		final var focus = computeFinalStateFocus(empire, finalStates);
		for (final State<L, P> state : finalStates) {
			queue.offer(state);
		}
		while (!queue.isEmpty()) {
			final var state = queue.poll();
			for (int i = 0; i < mNumLaws; i++) {
				final var j = i;
				final var currentFocus = focus.getImage(new Pair<>(state, j));
				if (currentFocus.isEmpty()) {
					continue;
				}
				final var predecessors = empire.internalPredecessors(state);
				for (final IncomingInternalTransition<Transition<L, P>, State<L, P>> incomingInternalTransition : predecessors) {
					final var predecessor = incomingInternalTransition.getPred();
					final var predecessorPair = new Pair<>(predecessor, j);
					final var transition = incomingInternalTransition.getLetter();
					final var focusedRegions =
							getFocusedRegions(predecessor, currentFocus, transition, focus.getImage(predecessorPair));
					final var added = focus.addAllPairs(predecessorPair, focusedRegions);
					if (added) {
						queue.offer(predecessor);
					}
				}
			}
		}
		return focus;
	}

	private Set<Region<P>> getFocusedRegions(final State<L, P> predecessor, final Set<Region<P>> successorFocus,
			final Transition<L, P> transition, final Set<Region<P>> predecessorFocus) {
		final var territory = predecessor.territory();
		final var bystanders = territory.getBystanders(transition);
		final var focusedBystanders = DataStructureUtils.intersection(bystanders, successorFocus);
		if (successorFocus.size() == focusedBystanders.size()) {
			return focusedBystanders;
		}

		var mayRegions = territory.getPlacesRegions(transition.getPredecessors());
		assert !mayRegions.isEmpty() : "territory enables transition but has no predecessor regions";

		final var alreadyFocused = DataStructureUtils.intersection(mayRegions, predecessorFocus);
		mayRegions = alreadyFocused.isEmpty() ? mayRegions : alreadyFocused;

		final var minRegion = mayRegions.stream().min(Comparator.comparingInt(Region::size));
		assert minRegion.isPresent() : "could not find best predecessor region";

		final var focused = new HashSet<>(focusedBystanders);
		focused.add(minRegion.orElseThrow());
		return focused;
	}

	private List<IPredicate> getSuccessorLaw(final List<IPredicate> laws, final Transition<L, P> transition) {
		final var succLaw = mProduct.internalSuccessors(laws, transition.getSymbol());
		return DataStructureUtils.getOneAndOnly(succLaw, "successor state").getSucc();
	}

	private HashRelation<Pair<State<L, P>, Integer>, Region<P>> computeFinalStateFocus(
			final NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>> empire,
			final Set<State<L, P>> finalStates) {
		final var focus = new HashRelation<Pair<State<L, P>, Integer>, Region<P>>();
		for (final State<L, P> state : finalStates) {
			final var territory = state.territory();
			final var enabledTransitions = territory.getEnabledTransitions(mNet);
			final var successorlessTransitions = enabledTransitions
					.filter(t -> !empire.internalSuccessors(state, t).iterator().hasNext()).collect(Collectors.toSet());
			for (final Transition<L, P> transition : successorlessTransitions) {
				final var successorLawList = getSuccessorLaw(state.laws(), transition);
				for (int i = 0; i < mNumLaws; i++) {
					if (!SmtUtils.isFalseLiteral(successorLawList.get(i).getFormula())) {
						continue;
					}
					var mayRegions = territory.getPlacesRegions(transition.getPredecessors());
					assert !mayRegions.isEmpty() : "territory enables transition but has no predecessor regions";

					final var j = i;
					final var alreadyFocused = mayRegions.stream()
							.filter(r -> focus.getImage(new Pair<>(state, j)).contains(r)).collect(Collectors.toSet());
					mayRegions = alreadyFocused.isEmpty() ? mayRegions : alreadyFocused;
					final var minRegion = mayRegions.stream().min(Comparator.comparingInt(Region::size));
					assert minRegion.isPresent() : "could not find best predecessor region";
					focus.addPair(new Pair<>(state, j), minRegion.orElseThrow());
				}
			}
		}
		return focus;
	}

	public Set<Region<P>> getLegalFocus(final State<L, P> state, final Integer lawIndex) {
		return mLegalFocus.getImage(new Pair<>(state, lawIndex));
	}

	public boolean isFocused(final P place, final State<L, P> state, final Integer lawIndex) {
		final var legalFocus = getLegalFocus(state, lawIndex);
		return legalFocus.stream().anyMatch(r -> r.contains(place));
	}

	@Override
	public List<IPredicate> getFocusedLaws(final State<L, P> state, final Region<P> region) {
		final List<IPredicate> focusedLaws = new ArrayList<>();
		final var laws = state.laws();
		for (int i = 0; i < mNumLaws; i++) {
			final var focus = getLegalFocus(state, i);
			if (focus.contains(region)) {
				focusedLaws.add(laws.get(i));
			}
		}
		return focusedLaws;
	}
}
