package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views;

import java.util.List;

public interface IRule<S> {
	boolean isApplicable(Configuration<S> config);

	List<Configuration<S>> successors(Configuration<S> config);

	int extensionSize();
}
