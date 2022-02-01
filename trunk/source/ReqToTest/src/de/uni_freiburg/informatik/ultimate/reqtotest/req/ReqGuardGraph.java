package de.uni_freiburg.informatik.ultimate.reqtotest.req;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableLabeledEdgesMultigraph;

public class ReqGuardGraph extends ModifiableLabeledEdgesMultigraph<ReqGuardGraph, TimedLabel> {

	private static final long serialVersionUID = -7450822163861915153L;
	private final int mNodeLabel;
	private final String mName;

	public ReqGuardGraph(final int label, final String name) {
		mNodeLabel = label;
		mName = name;
	}

	public int getLabel() {
		return mNodeLabel;
	}

	public String getName() {
		return mName;
	}

}