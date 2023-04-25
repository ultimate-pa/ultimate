package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

public class RabinUnion<LETTER, STATE> implements IRabinAutomaton<LETTER, STATE> {

	IRabinAutomaton<LETTER, STATE> mFirstAutomaton;
	IRabinAutomaton<LETTER, STATE> mSecondAutomaton;
	IRedGreenBlueStateFactory<STATE> mRGBFactory;
	HashSet<LETTER> mAlphabet;

	public RabinUnion(final IRabinAutomaton<LETTER, STATE> firstAutomaton,
			final IRabinAutomaton<LETTER, STATE> secondAutomaton, final IRedGreenBlueStateFactory<STATE> rgbFactory) {
		mFirstAutomaton = firstAutomaton;
		mSecondAutomaton = secondAutomaton;
		mRGBFactory = rgbFactory;
	}

	@Override
	public Set<LETTER> getAlphabet() {
		if (mAlphabet == null) {
			mAlphabet = new HashSet<>();
			mAlphabet.addAll(mFirstAutomaton.getAlphabet());
			mAlphabet.addAll(mSecondAutomaton.getAlphabet());
		}
		return mAlphabet;
	}

	@Override
	public int size() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public String sizeInformation() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IElement transformToUltimateModel(final AutomataLibraryServices services)
			throws AutomataOperationCanceledException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<STATE> getInitialStates() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isInitial(final STATE state) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isAccepting(final STATE state) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isFinite(final STATE state) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state, final LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

}
