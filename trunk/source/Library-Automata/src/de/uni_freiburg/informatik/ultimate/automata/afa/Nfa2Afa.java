package de.uni_freiburg.informatik.ultimate.automata.afa;

import java.util.Set;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;

/**
 * Provides a view of a given nondeterministic finite automaton as an alternating automaton.
 *
 * @param <L>
 *            the type of letters in the automaton
 * @param <S>
 *            the type of states in the automaton
 */
public class Nfa2Afa<L, S> implements IAlternatingFiniteAutomaton<L, S> {
	private final INwaOutgoingLetterAndTransitionProvider<L, S> mNFA;

	public Nfa2Afa(final INwaOutgoingLetterAndTransitionProvider<L, S> nfa) {
		mNFA = nfa;
		assert NestedWordAutomataUtils.isFiniteAutomaton(nfa);
	}

	@Override
	public Set<L> getAlphabet() {
		return mNFA.getAlphabet();
	}

	@Override
	public int size() {
		return mNFA.size();
	}

	@Override
	public Iterable<S> getInitialStates() {
		return mNFA.getInitialStates();
	}

	@Override
	public boolean isInitial(final S state) {
		return mNFA.isInitial(state);
	}

	@Override
	public boolean isFinal(final S state) {
		return mNFA.isFinal(state);
	}

	@Override
	public Bdd getSuccessors(final S state, final L letter, final BddFactory<S> bddFactory) {
		return StreamSupport.stream(mNFA.internalSuccessors(state, letter).spliterator(), false)
				.map(transition -> bddFactory.variable(transition.getSucc())).collect(bddFactory.toDisjunction());
	}
}
