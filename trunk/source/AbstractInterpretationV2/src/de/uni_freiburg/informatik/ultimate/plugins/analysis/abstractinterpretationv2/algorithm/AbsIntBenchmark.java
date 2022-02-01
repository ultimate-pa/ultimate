package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider.CsvColumn;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class AbsIntBenchmark<ACTION> implements ICsvProviderProvider<Object> {

	private final Map<Integer, Integer> mAction2Visits;
	private final Map<Integer, Integer> mAction2Merges;
	private final Map<Integer, Integer> mAction2Widen;
	private final Map<Integer, Integer> mAction2Fixpoints;
	private int mLastAction;

	@CsvColumn("MaxVariables")
	private int mMaxVariables;

	@CsvColumn("PostApplication")
	private int mPostApplication;
	private int mEvaluationRecursions;
	private int mEvaluationMaxRecursionDepth;
	private int mInverseEvaluationRecursions;
	private int mInverseEvaluationMaxRecursionDepth;

	public AbsIntBenchmark() {
		mAction2Visits = new HashMap<>();
		mAction2Merges = new HashMap<>();
		mAction2Widen = new HashMap<>();
		mAction2Fixpoints = new HashMap<>();
		mMaxVariables = 0;
		mPostApplication = 0;
		mEvaluationRecursions = 0;
		mEvaluationMaxRecursionDepth = 0;
		mInverseEvaluationRecursions = 0;
		mInverseEvaluationMaxRecursionDepth = 0;
	}

	@Override
	public ICsvProvider<Object> createCsvProvider() {
		return SimpleCsvProvider.constructCsvProviderReflectively(this);
	}

	void addIteration(final ACTION action) {
		mLastAction = action.hashCode();
		addOrIncrement(mAction2Visits);
	}

	void addMerge() {
		addOrIncrement(mAction2Merges);
	}

	void addWiden() {
		addOrIncrement(mAction2Widen);
	}

	void addFixpoint() {
		addOrIncrement(mAction2Fixpoints);
	}

	void addMaxVariables(final int varCount) {
		if (varCount > mMaxVariables) {
			mMaxVariables = varCount;
		}
	}

	void countPostApplication() {
		mPostApplication++;
	}

	public void recordEvaluationRecursionDepth(final int maxDepth) {
		if (maxDepth > mEvaluationMaxRecursionDepth) {
			mEvaluationMaxRecursionDepth = maxDepth;
		}
		mEvaluationRecursions++;
	}

	public void recordInverseEvaluationRecursionDepth(final int maxDepth) {
		if (maxDepth > mInverseEvaluationMaxRecursionDepth) {
			mInverseEvaluationMaxRecursionDepth = maxDepth;
		}
		mInverseEvaluationRecursions++;
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

		if (mEvaluationRecursions > 0) {
			sb.append("Performed ").append(mEvaluationRecursions)
					.append(" root evaluator evaluations with a maximum evaluation depth of ")
					.append(mEvaluationMaxRecursionDepth).append(". ");
		}

		if (mInverseEvaluationRecursions > 0) {
			sb.append("Performed ").append(mInverseEvaluationRecursions)
					.append(" inverse root evaluator evaluations with a maximum inverse evaluation depth of ")
					.append(mInverseEvaluationMaxRecursionDepth).append(". ");
		}

		if (mAction2Fixpoints.isEmpty()) {
			sb.append("Never found a fixpoint.");
		} else {
			final Optional<Integer> fixpoints =
					mAction2Fixpoints.entrySet().stream().map(a -> a.getValue()).reduce((a, b) -> a + b);
			sb.append("Found ").append(fixpoints.get()).append(" fixpoints after ").append(mAction2Fixpoints.size())
					.append(" different actions.");
		}
		sb.append(" Largest state had " + mMaxVariables + " variables.");

		return sb.toString();
	}
}
