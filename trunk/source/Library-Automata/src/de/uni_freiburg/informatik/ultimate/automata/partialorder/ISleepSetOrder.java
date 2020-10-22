package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.Comparator;

public interface ISleepSetOrder<S, L> {
	Comparator<L> getOrder(S state);
	
}
