package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis;

import de.uni_freiburg.informatik.ultimate.logic.Term;

public interface IEqualityProvidingState {

	boolean areEqual(Term t1, Term t2);
		
	boolean areUnequal(Term t1, Term t2);
	
	IEqualityProvidingState union(IEqualityProvidingState other);
}
