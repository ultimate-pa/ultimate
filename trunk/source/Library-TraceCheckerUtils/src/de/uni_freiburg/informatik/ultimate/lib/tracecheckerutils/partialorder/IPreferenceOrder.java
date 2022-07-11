package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.Comparator;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;

public interface IPreferenceOrder<L,S1,S2> {

	Comparator<L> getOrder(S1 stateProgram, S2 stateMonitor);
	
	boolean isPositional();
	
	public INwaOutgoingLetterAndTransitionProvider<L, S2> getMonitor();

}
