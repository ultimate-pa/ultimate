package de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.dfg;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;

public class DfgNode {
	private final IcfgEdge edge;

	public DfgNode(final IcfgEdge edge) {
		this.edge = edge;
	}

	public IcfgEdge getCorrespondingDFGEdge() {
		return edge;
	}

	@Override
	public String toString() {
		return edge.toString();
	}

}
