package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.Comparator;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class Preference2DfsOrder<L, S1, S2, S> implements IDfsOrder<L, S> {
	  private IPreferenceOrder<L, S1, S2> mPreferenceOrder;

	public Preference2DfsOrder(IPreferenceOrder<L, S1, S2> underlying, Function<S, Pair<S1, S2>> splitState) {
		  mPreferenceOrder = underlying;
	  }

	@Override
	public Comparator<L> getOrder(S state) {
		
		
		return mPreferenceOrder.getOrder(null, null);
	}

	@Override
	public boolean isPositional() {
		return true;
	}
	
	private Pair<S1, S2> splitState(){
		return null;
		
	}

	}
