package de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.walker;

import de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.visitors.SimpleRCFGVisitor;

public interface IRCFGVisitorDispatcher {
	void dispatch(SimpleRCFGVisitor visitor);
}
