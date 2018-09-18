package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates;

import java.util.Collection;
import java.util.concurrent.TimeUnit;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.statistics.Benchmark;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsElement;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsType;

public final class PredicateUnifierStatisticsGenerator implements IStatisticsDataProvider {

	private int mDeclaredPredicates = 0;
	private int mGetRequests = 0;
	private int mSyntacticMatches = 0;
	private int mSemanticMatches = 0;
	private int mConstructedPredicates = 0;
	private int mIntricatePredicates = 0;
	private int mDeprecatedPredicatesCount = 0;
	private int mImplicationChecksByTransitivity = 0;
	protected final Benchmark mBenchmark;

	protected boolean mRunning = false;

	public PredicateUnifierStatisticsGenerator() {
		mBenchmark = new Benchmark();
		mBenchmark.register(String.valueOf(PredicateUniferStatisticsDefinitions.Time));
	}

	public void incrementDeclaredPredicates() {
		mDeclaredPredicates++;
	}

	public void incrementGetRequests() {
		mGetRequests++;
	}

	public void incrementSyntacticMatches() {
		mSyntacticMatches++;
	}

	public void incrementSemanticMatches() {
		mSemanticMatches++;
	}

	public void incrementConstructedPredicates() {
		mConstructedPredicates++;
	}

	public void incrementIntricatePredicates() {
		mIntricatePredicates++;
	}

	public void incrementDeprecatedPredicates() {
		mDeprecatedPredicatesCount++;
	}

	public void incrementImplicationChecksByTransitivity() {
		mImplicationChecksByTransitivity++;
	}

	public long getTime() {
		return (long) mBenchmark.getElapsedTime(String.valueOf(PredicateUniferStatisticsDefinitions.Time),
				TimeUnit.NANOSECONDS);
	}

	public void continueTime() {
		assert !mRunning : "Timing already running";
		mRunning = true;
		mBenchmark.unpause(String.valueOf(PredicateUniferStatisticsDefinitions.Time));
	}

	public void stopTime() {
		assert mRunning : "Timing not running";
		mRunning = false;
		mBenchmark.pause(String.valueOf(PredicateUniferStatisticsDefinitions.Time));
	}

	@Override
	public Collection<String> getKeys() {
		return PredicateUnifierStatisticsType.getInstance().getKeys();
	}

	@Override
	public Object getValue(final String key) {
		final PredicateUniferStatisticsDefinitions keyEnum =
				Enum.valueOf(PredicateUniferStatisticsDefinitions.class, key);
		switch (keyEnum) {
		case DeclaredPredicates:
			return mDeclaredPredicates;
		case GetRequests:
			return mGetRequests;
		case SyntacticMatches:
			return mSyntacticMatches;
		case SemanticMatches:
			return mSemanticMatches;
		case ConstructedPredicates:
			return mConstructedPredicates;
		case IntricatePredicates:
			return mIntricatePredicates;
		case DeprecatedPredicates:
			return mDeprecatedPredicatesCount;
		case ImplicationChecksByTransitivity:
			return mImplicationChecksByTransitivity;
		case Time:
			return getTime();
		default:
			throw new AssertionError("unknown key");
		}
	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return PredicateUnifierStatisticsType.getInstance();
	}

	public static enum PredicateUniferStatisticsDefinitions implements IStatisticsElement {

		DeclaredPredicates(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

		GetRequests(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

		SyntacticMatches(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

		SemanticMatches(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

		ConstructedPredicates(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

		IntricatePredicates(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

		DeprecatedPredicates(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

		ImplicationChecksByTransitivity(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

		Time(Integer.class, StatisticsType.LONG_ADDITION, StatisticsType.NANOS_BEFORE_KEY),;

		private final Class<?> mClazz;
		private final Function<Object, Function<Object, Object>> mAggr;
		private final Function<String, Function<Object, String>> mPrettyprinter;

		PredicateUniferStatisticsDefinitions(final Class<?> clazz,
				final Function<Object, Function<Object, Object>> aggr,
				final Function<String, Function<Object, String>> prettyprinter) {
			mClazz = clazz;
			mAggr = aggr;
			mPrettyprinter = prettyprinter;
		}

		@Override
		public Object aggregate(final Object o1, final Object o2) {
			return mAggr.apply(o1).apply(o2);
		}

		@Override
		public String prettyprint(final Object o) {
			return mPrettyprinter.apply(name()).apply(o);
		}

		@Override
		public Class<?> getDataType() {
			return mClazz;
		}
	}

	public static class PredicateUnifierStatisticsType extends StatisticsType<PredicateUniferStatisticsDefinitions> {

		private static final PredicateUnifierStatisticsType INSTANCE = new PredicateUnifierStatisticsType();

		public PredicateUnifierStatisticsType() {
			super(PredicateUniferStatisticsDefinitions.class);
		}

		public static PredicateUnifierStatisticsType getInstance() {
			return INSTANCE;
		}
	}
}