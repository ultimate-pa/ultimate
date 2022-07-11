package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.Comparator;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;

public class Dfs2PreferenceOrder<L, S1, S2> implements IPreferenceOrder<L,S1,S2> {
	  private IDfsOrder<L,S1> mDFSOrder;

	public Dfs2PreferenceOrder(IDfsOrder<L,S1> underlying) {
		  mDFSOrder = underlying;
	  }

	@Override
	public Comparator<L> getOrder(S1 stateProgram, S2 stateMonitor) {
		return mDFSOrder.getOrder(stateProgram);
	}

	@Override
	public boolean isPositional() {
		return true;
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<L, S2> getMonitor() {
		return null;
	}

	}
