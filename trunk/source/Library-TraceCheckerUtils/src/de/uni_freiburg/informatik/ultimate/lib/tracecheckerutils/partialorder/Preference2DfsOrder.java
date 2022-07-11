package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.Comparator;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class Preference2DfsOrder<L, S1, S2, S> implements IDfsOrder<L, S> {
	  private IPreferenceOrder<L, S1, S2> mPreferenceOrder;
	private Function<S, Pair<S1, S2>> mSplitState;

	public Preference2DfsOrder(IPreferenceOrder<L, S1, S2> underlying, Function<S, Pair<S1, S2>> splitState) {
		  mPreferenceOrder = underlying;
		  mSplitState = splitState;
	  }

	@Override
	public Comparator<L> getOrder(S state) {
		
		Pair<S1,S2> statePair = mSplitState.apply(state);
		return mPreferenceOrder.getOrder(statePair.getFirst(), statePair.getSecond());
	}

	@Override
	public boolean isPositional() {
		return true;
	}

	}
