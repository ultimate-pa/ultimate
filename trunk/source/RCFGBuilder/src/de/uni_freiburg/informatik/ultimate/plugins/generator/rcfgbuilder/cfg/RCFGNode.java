package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import de.uni_freiburg.informatik.ultimate.model.Payload;
import de.uni_freiburg.informatik.ultimate.model.structure.ModifiableExplicitEdgesMultigraph;

public abstract class RCFGNode extends
		ModifiableExplicitEdgesMultigraph<RCFGNode, RCFGEdge> implements
		RcfgElement {

	protected RCFGNode(Payload payload) {
		super(payload);
	}

	protected RCFGNode() {
		super();
	}

	private static final long serialVersionUID = 1L;

}
