package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.function.UnaryOperator;

public class BroadcastRule<S> implements IRule<S> {
	private final S mSource;
	private final S mTarget;
	private final UnaryOperator<S> mBroadcast;

	public BroadcastRule(final S source, final S target, final UnaryOperator<S> broadcast) {
		mSource = source;
		mTarget = target;
		mBroadcast = broadcast;
	}

	@Override
	public boolean isApplicable(final Configuration<S> config) {
		return config.stream().anyMatch(mSource::equals);
	}

	@Override
	public List<Configuration<S>> successors(final Configuration<S> config) {
		final var result = new ArrayList<Configuration<S>>();

		for (int i = 0; i < config.size(); ++i) {
			final var state = config.get(i);
			if (mSource.equals(state)) {
				result.add(successor(config, i));
			}
		}

		return result;
	}

	private Configuration<S> successor(final Configuration<S> config, final int index) {
		final var subst = new HashMap<Integer, S>();
		subst.put(index, mTarget);

		for (int i = 0; i < config.size(); ++i) {
			final var state = config.get(i);
			final var newState = mBroadcast.apply(state);
			if (i != index && newState != null) {
				subst.put(i, newState);
			}
		}

		return config.replace(subst);
	}

	@Override
	public int extensionSize() {
		return 1;
	}
}
