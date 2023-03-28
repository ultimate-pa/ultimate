package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

/**
 * Wraps a Büchi-automton (represented by {@link INwaOutgoingLetterAndTransitionProvider}) into an
 * {@link IRabinAutomaton}.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class Buchi2RabinAutomaton<LETTER, STATE> implements IRabinAutomaton<LETTER, STATE> {
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mUnderlying;

	public Buchi2RabinAutomaton(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> underlying) {
		// TODO: Should we check that underlying has no call/return edges?
		mUnderlying = underlying;
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mUnderlying.getAlphabet();
	}

	@Override
	public int size() {
		return mUnderlying.size();
	}

	@Override
	public String sizeInformation() {
		return mUnderlying.sizeInformation();
	}

	@Override
	public IElement transformToUltimateModel(final AutomataLibraryServices services)
			throws AutomataOperationCanceledException {
		return mUnderlying.transformToUltimateModel(services);
	}

	@Override
	public Iterable<STATE> getInitialStates() {
		return mUnderlying.getInitialStates();
	}

	@Override
	public boolean isInitial(final STATE state) {
		return mUnderlying.isInitial(state);
	}

	@Override
	public boolean isAccepting(final STATE state) {
		return mUnderlying.isFinal(state);
	}

	@Override
	public boolean isFinite(final STATE state) {
		return false;
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state) {
		return mUnderlying.internalSuccessors(state);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state, final LETTER letter) {
		return mUnderlying.internalSuccessors(state, letter);
	}
}
