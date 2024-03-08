package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views;

import java.util.ArrayList;
import java.util.List;

public class LocalRule<S> implements IRule<S> {
	private final S mSource;
	private final S mTarget;

	public LocalRule(final S source, final S target) {
		mSource = source;
		mTarget = target;
	}

	@Override
	public boolean isApplicable(final Configuration<S> config) {
		return config.contains(mSource);
	}

	@Override
	public List<Configuration<S>> successors(final Configuration<S> config) {
		final var result = new ArrayList<Configuration<S>>();

		for (int i = 0; i < config.size(); ++i) {
			final S state = config.get(i);
			if (state.equals(mSource)) {
				result.add(config.replace(i, mTarget));
			}
		}
		return result;
	}

	@Override
	public int extensionSize() {
		return 0;
	}
}
