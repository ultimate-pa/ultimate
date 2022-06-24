package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.Comparator;

public interface IParameterizedOrder<L,S> {

	Comparator<L> getOrder(S state);
	
	boolean isPositional();
	
	boolean isStep();
}
