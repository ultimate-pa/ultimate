package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class ConnectedRegion<L, P> extends Region<P> {

	ImmutableSet<Transition<L, P>> mTransitions;

	public ConnectedRegion(final ImmutableSet<P> region, final ImmutableSet<Transition<L, P>> transitions) {
		super(region);
		mTransitions = transitions;
	}

	ImmutableSet<Transition<L, P>> getTransitions() {
		return mTransitions;
	}
}
