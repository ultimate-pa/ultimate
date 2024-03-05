package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views;

import java.util.ArrayList;
import java.util.List;

public class LocalRule<S> implements IRule<S> {
	private final S mPredecessor;
	private final S mSuccessor;

	private LocalRule(final S predecessor, final S successor) {
		mPredecessor = predecessor;
		mSuccessor = successor;
	}

	@Override
	public boolean isApplicable(final Configuration<S> config) {
		return config.contains(mPredecessor);
	}

	@Override
	public List<Configuration<S>> successors(final Configuration<S> config) {
		final var result = new ArrayList<Configuration<S>>();

		for (int i = 0; i < config.size(); ++i) {
			final S state = config.get(i);
			if (state.equals(mPredecessor)) {
				result.add(config.replace(i, mSuccessor));
			}
		}
		return result;
	}

	@Override
	public int extensionSize() {
		return 0;
	}
}
