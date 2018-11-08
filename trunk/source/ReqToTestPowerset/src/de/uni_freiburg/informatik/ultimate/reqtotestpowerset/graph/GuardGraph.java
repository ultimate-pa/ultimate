package de.uni_freiburg.informatik.ultimate.reqtotestpowerset.graph;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableLabeledEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class GuardGraph extends ModifiableLabeledEdgesMultigraph<GuardGraph, Term> {

	private static final long serialVersionUID = 94683849463494167L;
	private final int mNodeLabel;
	
	public GuardGraph(int label) {
		mNodeLabel = label;
	}

	public int getLabel() {
		return mNodeLabel;
	}
}
