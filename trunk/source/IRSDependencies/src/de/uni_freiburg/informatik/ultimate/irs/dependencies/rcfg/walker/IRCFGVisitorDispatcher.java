package de.uni_freiburg.informatik.ultimate.irs.dependencies.rcfg.walker;

import de.uni_freiburg.informatik.ultimate.irs.dependencies.rcfg.visitors.RCFGVisitor;

public interface IRCFGVisitorDispatcher {
	void dispatch(RCFGVisitor visitor);
}
