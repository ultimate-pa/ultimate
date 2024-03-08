package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Predicate;

public class GlobalRule<S> implements IRule<S> {
	public enum Quantifier {
		EXISTS(false), FORALL(true);

		private final boolean mDefaultValue;

		Quantifier(final boolean defaultValue) {
			mDefaultValue = defaultValue;
		}

		public boolean defaultValue() {
			return mDefaultValue;
		}

		public boolean combine(final boolean oldValue, final boolean newValue) {
			switch (this) {
			case EXISTS:
				return oldValue || newValue;
			case FORALL:
				return oldValue && newValue;
			}
			throw new IllegalArgumentException("Unknown quantifier: " + this);
		}
	}

	public enum Range {
		LESS, GREATER, DISTINCT;

		public boolean satisfies(final int i, final int referencePoint) {
			switch (this) {
			case DISTINCT:
				return i != referencePoint;
			case GREATER:
				return i > referencePoint;
			case LESS:
				return i < referencePoint;
			}
			throw new IllegalArgumentException("Unknown range: " + this);
		}
	}

	private final S mSource;
	private final S mTarget;
	private final Range mRange;
	private final Quantifier mQuantifier;
	private final Predicate<S> mCondition;

	public GlobalRule(final S source, final S target, final Range range, final Quantifier quantifier,
			final Predicate<S> condition) {
		mSource = source;
		mTarget = target;
		mRange = range;
		mQuantifier = quantifier;
		mCondition = condition;
	}

	@Override
	public boolean isApplicable(final Configuration<S> config) {
		for (int i = 0; i < config.size(); ++i) {
			final var state = config.get(i);
			if (state.equals(mSource)) {
				final boolean conditionSatisfied = checkCondition(config, i);
				if (conditionSatisfied) {
					return true;
				}
			}
		}
		return false;
	}

	private boolean checkCondition(final Configuration<S> config, final int index) {
		boolean result = mQuantifier.defaultValue();
		for (int i = 0; i < config.size(); ++i) {
			if (mRange.satisfies(i, index)) {
				final var state = config.get(i);
				result = mQuantifier.combine(result, mCondition.test(state));
			}
		}
		return result;
	}

	@Override
	public List<Configuration<S>> successors(final Configuration<S> config) {
		assert isApplicable(config);

		final var result = new ArrayList<Configuration<S>>();
		for (int i = 0; i < config.size(); ++i) {
			final var state = config.get(i);
			if (state.equals(mSource)) {
				result.add(config.replace(i, mTarget));
			}

		}
		return result;
	}

	@Override
	public int extensionSize() {
		return mQuantifier == Quantifier.EXISTS ? 0 : 1;
	}
}
