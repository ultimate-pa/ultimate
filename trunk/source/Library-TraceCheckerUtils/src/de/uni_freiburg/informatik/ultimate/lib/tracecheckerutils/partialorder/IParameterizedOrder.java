package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.Comparator;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.ParameterizedOrderAutomaton.State;

public interface IParameterizedOrder<L,State,S2> {

	Comparator<L> getOrder(State stateParameterized, S2 stateProgram);
	
	boolean isPositional();
	
	public INwaOutgoingLetterAndTransitionProvider<L, State> getParameterizedOrderAutomaton();

}
