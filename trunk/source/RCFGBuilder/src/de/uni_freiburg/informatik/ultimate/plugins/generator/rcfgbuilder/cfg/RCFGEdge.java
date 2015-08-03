package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.structure.ModifiableMultigraphEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.IRCFGVisitor;

public abstract class RCFGEdge extends
		ModifiableMultigraphEdge<RCFGNode, RCFGEdge> implements RcfgElement {

	protected RCFGEdge(RCFGNode source, RCFGNode target, IPayload payload) {
		super(source, target, payload);
	}

	private static final long serialVersionUID = 1L;

	public abstract void accept(IRCFGVisitor visitor);
}
