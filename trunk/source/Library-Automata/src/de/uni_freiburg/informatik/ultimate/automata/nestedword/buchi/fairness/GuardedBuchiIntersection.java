package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.fairness;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public class GuardedBuchiIntersection<LETTER, STATE, GUARD>
		implements IGuardedAutomaton<LETTER, ProductState<STATE>, GUARD> {
	private final List<? extends IGuardedAutomaton<LETTER, STATE, GUARD>> mAutomata;
	private final Function<List<GUARD>, GUARD> mGuardCombinator;

	public GuardedBuchiIntersection(final List<? extends IGuardedAutomaton<LETTER, STATE, GUARD>> automata,
			final Function<List<GUARD>, GUARD> guardCombinator) {
		mAutomata = automata;
		mGuardCombinator = guardCombinator;
	}

	@Override
	public Set<ProductState<STATE>> getInitialStates() {
		Set<ProductState<STATE>> result = Set.of(new ProductState<STATE>(List.of(), 0));
		for (final var a : mAutomata) {
			final Set<ProductState<STATE>> newResult = new HashSet<>();
			for (final STATE state : a.getInitialStates()) {
				for (final ProductState<STATE> ps : result) {
					newResult.add(ps.extend(state));
				}
			}
			result = newResult;
		}
		return result;
	}

	@Override
	public boolean isAccepting(final ProductState<STATE> state) {
		final int index = mAutomata.size() - 1;
		return state.getIndex() == index && mAutomata.get(index).isAccepting(state.getState(index));
	}

	@Override
	public Set<LETTER> getAlphabet() {
		// TODO: Check that they have the same alphabet
		return mAutomata.getFirst().getAlphabet();
	}

	@Override
	public Set<Triple<LETTER, GUARD, ProductState<STATE>>> getSuccessors(final ProductState<STATE> state,
			final LETTER letter) {
		Set<List<Triple<LETTER, GUARD, STATE>>> transitionCombinations = Set.of(List.of());
		for (int i = 0; i < mAutomata.size(); i++) {
			final var succs = mAutomata.get(i).getSuccessors(state.getState(i), letter);
			if (succs.isEmpty()) {
				return Set.of();
			}
			final Set<List<Triple<LETTER, GUARD, STATE>>> transitionCombinationsNew = new HashSet<>();
			for (final var s : succs) {
				for (final var t : transitionCombinations) {
					transitionCombinationsNew.add(DataStructureUtils.concat(t, List.of(s)));
				}
			}
			transitionCombinations = transitionCombinationsNew;
		}
		final int newIndex = mAutomata.get(state.getIndex()).isAccepting(state.getState(state.getIndex()))
				? ((state.getIndex() + 1) % mAutomata.size())
				: state.getIndex();
		return transitionCombinations.stream().map(x -> computeTransitionProduct(x, newIndex))
				.collect(Collectors.toSet());
	}

	private Triple<LETTER, GUARD, ProductState<STATE>>
			computeTransitionProduct(final List<Triple<LETTER, GUARD, STATE>> transitions, final int index) {
		final GUARD newGuard = mGuardCombinator.apply(transitions.stream().map(Triple::getSecond).toList());
		final ProductState<STATE> newSucc =
				new ProductState<>(transitions.stream().map(Triple::getThird).toList(), index);
		return new Triple<>(transitions.getFirst().getFirst(), newGuard, newSucc);
	}

	@Override
	public Set<GUARD> getGuards(final LETTER letter) {
		Set<List<GUARD>> guards = Set.of(List.of());
		for (final var a : mAutomata) {
			final Set<List<GUARD>> newGuards = new HashSet<>();
			for (final var g : guards) {
				for (final var g2 : a.getGuards(letter)) {
					newGuards.add(DataStructureUtils.concat(g, List.of(g2)));
				}
			}
			guards = newGuards;
		}
		return guards.stream().map(mGuardCombinator).collect(Collectors.toSet());
	}
}
