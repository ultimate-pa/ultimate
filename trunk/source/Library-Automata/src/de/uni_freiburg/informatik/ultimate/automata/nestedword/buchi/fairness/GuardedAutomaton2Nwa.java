package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.fairness;

import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class GuardedAutomaton2Nwa<LETTER, STATE, GUARD>
		implements INwaOutgoingLetterAndTransitionProvider<Pair<LETTER, GUARD>, STATE> {
	private final IGuardedAutomaton<LETTER, STATE, GUARD> mUnderlying;

	public GuardedAutomaton2Nwa(final IGuardedAutomaton<LETTER, STATE, GUARD> underlying) {
		mUnderlying = underlying;
	}

	@Override
	public VpAlphabet<Pair<LETTER, GUARD>> getVpAlphabet() {
		return new VpAlphabet<>(mUnderlying.getAlphabet().stream()
				.flatMap(x -> mUnderlying.getGuards(x).stream().map(y -> new Pair<>(x, y)))
				.collect(Collectors.toSet()));
	}

	@Override
	public STATE getEmptyStackState() {
		// TODO: Calls/Returns are not supported yet.
		return null;
	}

	@Override
	public Iterable<STATE> getInitialStates() {
		return mUnderlying.getInitialStates();
	}

	@Override
	public boolean isInitial(final STATE state) {
		return mUnderlying.getInitialStates().contains(state);
	}

	@Override
	public boolean isFinal(final STATE state) {
		return mUnderlying.isAccepting(state);
	}

	@Override
	public int size() {
		return 0;
	}

	@Override
	public String sizeInformation() {
		return "unknown";
	}

	@Override
	public Iterable<OutgoingInternalTransition<Pair<LETTER, GUARD>, STATE>> internalSuccessors(final STATE state,
			final Pair<LETTER, GUARD> letter) {
		return () -> mUnderlying.getSuccessors(state, letter.getFirst()).stream()
				.filter(x -> x.getSecond().equals(letter.getSecond()))
				.map(x -> new OutgoingInternalTransition<>(new Pair<>(x.getFirst(), x.getSecond()), x.getThird()))
				.iterator();
	}

	@Override
	public Iterable<OutgoingCallTransition<Pair<LETTER, GUARD>, STATE>> callSuccessors(final STATE state,
			final Pair<LETTER, GUARD> letter) {
		// TODO: Calls/Returns are not supported yet.
		return List.of();
	}

	@Override
	public Iterable<OutgoingReturnTransition<Pair<LETTER, GUARD>, STATE>> returnSuccessors(final STATE state,
			final STATE hier, final Pair<LETTER, GUARD> letter) {
		// TODO: Calls/Returns are not supported yet.
		return List.of();
	}
}
