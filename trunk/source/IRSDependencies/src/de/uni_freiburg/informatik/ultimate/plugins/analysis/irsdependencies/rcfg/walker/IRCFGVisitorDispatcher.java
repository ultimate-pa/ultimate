package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.walker;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.visitors.SimpleRCFGVisitor;

public interface IRCFGVisitorDispatcher {
	void dispatch(SimpleRCFGVisitor visitor);
}
