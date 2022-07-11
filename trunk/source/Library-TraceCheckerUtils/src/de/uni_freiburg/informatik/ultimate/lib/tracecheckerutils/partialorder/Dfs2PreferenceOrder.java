package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.Comparator;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.ParameterizedOrderAutomaton.State;

public class Dfs2PreferenceOrder<L, S> implements IPreferenceOrder<L,State,S> {
	  private IDfsOrder<S, L> mDFSOrder;

	public Dfs2PreferenceOrder(IDfsOrder<S, L> underlying) {
		  mDFSOrder = underlying;
	  }

	@Override
	public Comparator<L> getOrder(State stateMonitor, S stateProgram) {
		
		return null; //die order hängt bei der IPreferenceOrder ausschließlich vom stateMonitor ab, aber dieser existiert für die IDfsOrder nicht
	}

	@Override
	public boolean isPositional() {
		return true;
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<L, State> getMonitor() {
		return null;
	}

	}
