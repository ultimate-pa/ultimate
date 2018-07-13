package de.uni_freiburg.informatik.ultimate.reqtotest;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableLabeledEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class ReqGuardGraph extends ModifiableLabeledEdgesMultigraph<ReqGuardGraph, Term> {
	
	private static final long serialVersionUID = -7450822163861915153L;
	private final int mNodeLabel;
	
	public ReqGuardGraph(int label) {
		mNodeLabel = label;
	}
	
	public int getLabel() {
		return mNodeLabel;
	}

}
