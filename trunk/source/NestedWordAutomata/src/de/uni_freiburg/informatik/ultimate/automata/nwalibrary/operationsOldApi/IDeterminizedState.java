package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi;

import java.util.Set;

public interface IDeterminizedState<LETTER, STATE> {

	public abstract Set<STATE> getDownStates();

	public abstract Set<STATE> getUpStates(STATE caller);

}