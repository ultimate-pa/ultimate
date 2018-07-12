package de.uni_freiburg.informatik.ultimate.reqtotest;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableLabeledEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class ReqGuardGraph<T> extends ModifiableLabeledEdgesMultigraph<ReqGuardGraph<T>, Term> {
	
	private final T mNodeLabel;
	
	public ReqGuardGraph(T label) {
		mNodeLabel = label;
	}
	
	public T getLabel() {
		return mNodeLabel;
	}

}
