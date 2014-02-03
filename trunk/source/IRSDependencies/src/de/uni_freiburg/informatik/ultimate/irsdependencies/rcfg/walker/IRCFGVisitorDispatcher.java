package de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.walker;

import de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.visitors.RCFGVisitor;

public interface IRCFGVisitorDispatcher {
	void dispatch(RCFGVisitor visitor);
}
