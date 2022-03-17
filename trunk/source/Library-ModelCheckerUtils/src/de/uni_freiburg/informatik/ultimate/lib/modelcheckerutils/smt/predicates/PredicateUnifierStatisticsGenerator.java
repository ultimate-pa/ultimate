package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil.Reflected;
import de.uni_freiburg.informatik.ultimate.util.statistics.BaseStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.DefaultMeasureDefinitions;
import de.uni_freiburg.informatik.ultimate.util.statistics.measures.TimeTracker;

public final class PredicateUnifierStatisticsGenerator extends BaseStatisticsDataProvider {

	public static final String PREDICATE_UNIFIER_TIME = "PredicateUnifierTime";

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mDeclaredPredicates;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mGetRequests;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mSyntacticMatches;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mSemanticMatches;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mConstructedPredicates;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mIntricatePredicates;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mDeprecatedPredicatesCount;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mImplicationChecksByTransitivity;

	@Reflected(prettyName = PREDICATE_UNIFIER_TIME)
	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mTime;

	public PredicateUnifierStatisticsGenerator(final IToolchainStorage storage) {
		super(storage);
		mTime = new TimeTracker();
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

	public void startTime() {
		mTime.start();
	}

	public void stopTime() {
		mTime.stop();
	}
}