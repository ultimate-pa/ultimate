package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class AbstractInterpretationBenchmark<ACTION, LOCATION> implements ICsvProviderProvider<Object> {

	private final Map<Integer, Integer> mAction2Visits;
	private final Map<Integer, Integer> mAction2Merges;
	private final Map<Integer, Integer> mAction2Widen;
	private final Map<Integer, Integer> mAction2Fixpoints;
	private int mLastAction;

	public AbstractInterpretationBenchmark() {
		mAction2Visits = new HashMap<>();
		mAction2Merges = new HashMap<>();
		mAction2Widen = new HashMap<>();
		mAction2Fixpoints = new HashMap<>();
	}

	@Override
	public ICsvProvider<Object> createCsvProvider() {
		return null;
	}

	public void addIteration(final ACTION action) {
		mLastAction = action.hashCode();
		addOrIncrement(mAction2Visits);
	}

	public void addMerge() {
		addOrIncrement(mAction2Merges);
	}

	public void addWiden() {
		addOrIncrement(mAction2Widen);
	}

	public void addFixpoint() {
		addOrIncrement(mAction2Fixpoints);
	}

	private void addOrIncrement(final Map<Integer, Integer> map) {
		final Integer visits = map.get(mLastAction);
		if (visits == null) {
			map.put(mLastAction, 1);
		} else {
			map.put(mLastAction, visits + 1);
		}
	}

	@Override
	public String toString() {
		if (mAction2Visits.isEmpty()) {
			return "No benchmarks available";
		}
		final StringBuilder sb = new StringBuilder();
		final Optional<Integer> visits =
				mAction2Visits.entrySet().stream().map(a -> a.getValue()).reduce((a, b) -> a + b);
		sb.append("Visited ").append(mAction2Visits.size()).append(" different actions ").append(visits.get())
				.append(" times. ");

		if (mAction2Merges.isEmpty()) {
			sb.append("Never merged. ");
		} else {
			final Optional<Integer> merges =
					mAction2Merges.entrySet().stream().map(a -> a.getValue()).reduce((a, b) -> a + b);
			sb.append("Merged at ").append(mAction2Merges.size()).append(" different actions ").append(merges.get())
					.append(" times. ");
		}

		if (mAction2Widen.isEmpty()) {
			sb.append("Never widened. ");
		} else {
			final Optional<Integer> widen =
					mAction2Widen.entrySet().stream().map(a -> a.getValue()).reduce((a, b) -> a + b);
			sb.append("Widened at ").append(mAction2Widen.size()).append(" different actions ").append(widen.get())
					.append(" times. ");
		}

		if (mAction2Fixpoints.isEmpty()) {
			sb.append("Never found a fixpoint.");
		} else {
			final Optional<Integer> fixpoints =
					mAction2Fixpoints.entrySet().stream().map(a -> a.getValue()).reduce((a, b) -> a + b);
			sb.append("Found ").append(fixpoints.get()).append(" fixpoints after ").append(mAction2Fixpoints.size())
					.append(" different actions.");
		}

		return sb.toString();
	}
}
