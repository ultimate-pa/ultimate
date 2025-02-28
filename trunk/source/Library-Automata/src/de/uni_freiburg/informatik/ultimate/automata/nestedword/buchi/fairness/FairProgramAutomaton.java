package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.fairness;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public class FairProgramAutomaton<LETTER, STATE, STATE2, GUARD>
		implements INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> {
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mProgramAutomaton;
	private final IGuardedAutomaton<LETTER, STATE2, GUARD> mFairnessAutomaton;
	private final IFairnessStateFactory<STATE, STATE2, LETTER, GUARD> mStateFactory;

	private final Map<Triple<LETTER, GUARD, Set<LETTER>>, LETTER> mNewLetterCache = new HashMap<>();

	public FairProgramAutomaton(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> programAutomaton,
			final IGuardedAutomaton<LETTER, STATE2, GUARD> fairnessAutomaton,
			final IFairnessStateFactory<STATE, STATE2, LETTER, GUARD> stateFactory) {
		mProgramAutomaton = programAutomaton;
		mFairnessAutomaton = fairnessAutomaton;
		mStateFactory = stateFactory;
	}

	@Override
	public VpAlphabet<LETTER> getVpAlphabet() {
		// TODO: The alphabet will be constructed on-demand. Is this an issue?
		return new VpAlphabet<>(new HashSet<>(mNewLetterCache.values()));
	}

	@Override
	public STATE getEmptyStackState() {
		// TODO: Calls/Returns are not supported yet.
		return null;
	}

	@Override
	public Iterable<STATE> getInitialStates() {
		final List<STATE> result = new ArrayList<>();
		for (final var s1 : mProgramAutomaton.getInitialStates()) {
			for (final var s2 : mFairnessAutomaton.getInitialStates()) {
				result.add(mStateFactory.combineStates(s1, s2));
			}
		}
		return result;
	}

	@Override
	public boolean isInitial(final STATE state) {
		final var statePair = mStateFactory.getOriginalStates(state);
		return mProgramAutomaton.isInitial(statePair.getFirst())
				&& mFairnessAutomaton.getInitialStates().contains(statePair.getSecond());
	}

	@Override
	public boolean isFinal(final STATE state) {
		final var statePair = mStateFactory.getOriginalStates(state);
		return mProgramAutomaton.isFinal(statePair.getFirst()) && mFairnessAutomaton.isAccepting(statePair.getSecond());
	}

	@Override
	public int size() {
		return 0;
	}

	@Override
	public String sizeInformation() {
		return "unknown, on demand constuction";
	}

	private List<OutgoingInternalTransition<LETTER, STATE>> getProductEdges(final STATE state,
			final Set<LETTER> letters) {
		final var statePair = mStateFactory.getOriginalStates(state);
		final Set<LETTER> enabledActions = mStateFactory.getEnabledActions(statePair.getFirst());
		// StreamSupport.stream(mProgramAutomaton.internalSuccessors(statePair.getFirst()).spliterator(), false)
		// .map(x -> x.getLetter()).collect(Collectors.toSet());
		// TODO: Since we already compute all the outgoing edges in lettersInternal (but keep only the letters), it
		// might be sensible to cache the edges to avoid duplicate computation.
		final List<OutgoingInternalTransition<LETTER, STATE>> result = new ArrayList<>();
		for (final LETTER letter : letters) {
			for (final var edge1 : mProgramAutomaton.internalSuccessors(statePair.getFirst(), letter)) {
				for (final var edge2 : mFairnessAutomaton.getSuccessors(statePair.getSecond(), letter)) {
					final LETTER newLetter;
					if (mStateFactory.isTrivial(edge2.getSecond())) {
						newLetter = letter;
					} else {
						newLetter =
								mNewLetterCache.computeIfAbsent(new Triple<>(letter, edge2.getSecond(), enabledActions),
										x -> mStateFactory.combineGuard(x.getFirst(), x.getSecond(), x.getThird()));
						if (mStateFactory.isInfeasible(newLetter)) {
							continue;
						}
					}
					final STATE newState = mStateFactory.combineStates(edge1.getSucc(), edge2.getThird());
					result.add(new OutgoingInternalTransition<>(newLetter, newState));
				}
			}
		}
		return result;
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state,
			final LETTER letter) {
		return getProductEdges(state, Set.of(letter));
	}

	@Override
	public Set<LETTER> lettersInternal(final STATE state) {
		// The default implementation calls getVpAlphabet() here. This does not work, since we create the alphabet
		// on-demand, therefore we already compute all outgoing edges here.
		return getProductEdges(state, mProgramAutomaton.lettersInternal(state)).stream().map(x -> x.getLetter())
				.collect(Collectors.toSet());
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state, final LETTER letter) {
		// TODO: Calls/Returns are not supported yet.
		return List.of();
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final STATE hier,
			final LETTER letter) {
		// TODO: Calls/Returns are not supported yet.
		return List.of();
	}
}
