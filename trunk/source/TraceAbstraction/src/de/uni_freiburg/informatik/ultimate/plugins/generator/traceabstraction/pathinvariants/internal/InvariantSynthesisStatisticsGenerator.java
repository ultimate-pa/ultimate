package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.LinearInequalityInvariantPatternProcessor.LinearInequalityPatternProcessorStatistics;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil.Reflected;
import de.uni_freiburg.informatik.ultimate.util.statistics.BaseStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.DefaultMeasureDefinitions;
import de.uni_freiburg.informatik.ultimate.util.statistics.measures.StringCounter;

public class InvariantSynthesisStatisticsGenerator extends BaseStatisticsDataProvider {

	// the sum of path program size (measured as the number of inequalities of all transformulas) for each overall
	// iteration
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mProgramSizeConjuncts;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mProgramSizeDisjuncts;

	// the sum of path program locations for each overall iteration
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mProgramLocs;

	// the sum of path program locations for each overall iteration after Lbe has been applied
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mProgramLocsLbe;

	// the sum of path program variables for each overall iteration
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mProgramVars;

	// the sum of template inequalities per location per round per iteration
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mSumOfTemplateInequalities;

	// the minimum size of all templates occurring in the most recent round
	@Statistics(type = DefaultMeasureDefinitions.INT_MAX)
	private int mSizeOfLargestTemplate;

	// the minimum size of all templates occurring in the most recent round
	@Statistics(type = DefaultMeasureDefinitions.INT_MAX)
	private int mSizeOfSmallestTemplate;

	// the maximum of the sum of template inequalities per round
	@Statistics(type = DefaultMeasureDefinitions.INT_MAX)
	private int mMaxNumOfInequalities;

	// the maximum number of rounds
	@Statistics(type = DefaultMeasureDefinitions.INT_MAX)
	private int mMaxRound;

	// the sum of variables per location per round
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mSumVarsPerLoc;

	// the sum of the difference of all variables and the live variables per location per round
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mSumNonLiveVarsPerLoc;

	// the sum of the difference of all variables and the variables from the unsat core per location per round
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mSumNonUnsatCoreLocs;

	// the sum of the difference of all variables and the variables from the unsat core per location per round
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mSumNonUnsatCoreVars;

	// the maximum DAG-size of (the sum of template inequalities per location per round) for normal constraints
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mTreeSizeNormalConstr;

	// the maximum DAG-size of (the sum of template inequalities per location per round) for constraints of Under-
	// and/or Overapproximations
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mTreeSizeApproxConstr;

	// Number of Motzkin Transformations for normal constraints
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mMotzkinTransformationsNormalConstr;

	// Number of Motzkin Transformations for constraints of Under- and/or Overapproximations
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mMotzkinTransformationsApproxConstr;

	// Number of Motzkin Coefficients needed for normal constraints
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mMotzkinCoefficientsNormalConstr;

	// Number of Motzkin Coefficients needed for constraints of Under- and/or Overapproximations
	@Reflected(prettyName = "MotzkinCoefficientsApproxConstr")
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mMotzkinCoefficientsApproxConstr;

	// the sum of the time needed per round to solve the constraints
	@Statistics(type = DefaultMeasureDefinitions.LONG_TIME)
	private long mConstraintsSolvingTime;

	// the sum of the time needed per round to construct the constraints
	@Statistics(type = DefaultMeasureDefinitions.LONG_TIME)
	private long mConstraintsConstructionTime;

	// Sat status
	@Statistics(type = DefaultMeasureDefinitions.STRING_COUNTER)
	private final StringCounter mSatStatus = new StringCounter();

	protected InvariantSynthesisStatisticsGenerator(final IToolchainStorage storage) {
		super(storage);
	}

	public void setNumOfPathProgramLocations(final int numOfLocsBeforeLbe, final int numOfLocsAfterLbe) {
		mProgramLocs = numOfLocsBeforeLbe;
		mProgramLocsLbe = numOfLocsAfterLbe;

	}

	public void setNumOfVars(final int numOfVars) {
		mProgramVars = numOfVars;
	}

	public void addStatisticsDataBeforeCheckSat(final int numOfTemplateInequalitiesForThisRound,
			final int maximalTemplateSizeOfThisRound, final int minimalTemplateSizeOfThisRound,
			final int sumOfVarsPerLoc, final int numfOfNonLiveVariables, final int round) {
		if (numOfTemplateInequalitiesForThisRound > mMaxNumOfInequalities) {
			mMaxNumOfInequalities = numOfTemplateInequalitiesForThisRound;
		}
		mSumOfTemplateInequalities += numOfTemplateInequalitiesForThisRound;
		mSumVarsPerLoc += sumOfVarsPerLoc;
		mSumNonLiveVarsPerLoc += numfOfNonLiveVariables;
		if (round > mMaxRound) {
			mMaxRound = round;
		}
		if (maximalTemplateSizeOfThisRound > mSizeOfLargestTemplate) {
			mSizeOfLargestTemplate = maximalTemplateSizeOfThisRound;
		}
		mSizeOfSmallestTemplate = minimalTemplateSizeOfThisRound;
	}

	public void addStatisticsDataAfterCheckSat(final int numOfNonUnsatCoreLocs, final int numOfNonUnsatCoreVars,
			final String satResult,
			final Map<LinearInequalityPatternProcessorStatistics, Object> linearInequalityStats) {
		mProgramSizeConjuncts =
				(Integer) linearInequalityStats.get(LinearInequalityPatternProcessorStatistics.ProgramSizeConjuncts);
		mProgramSizeDisjuncts =
				(Integer) linearInequalityStats.get(LinearInequalityPatternProcessorStatistics.ProgramSizeDisjuncts);

		mTreeSizeNormalConstr += (Integer) linearInequalityStats
				.get(LinearInequalityPatternProcessorStatistics.TreesizeNormalConstraints);
		mTreeSizeApproxConstr += (Integer) linearInequalityStats
				.get(LinearInequalityPatternProcessorStatistics.TreesizeApproxConstraints);

		mMotzkinTransformationsNormalConstr += (Integer) linearInequalityStats
				.get(LinearInequalityPatternProcessorStatistics.MotzkinTransformationsNormalConstraints);
		mMotzkinTransformationsApproxConstr += (Integer) linearInequalityStats
				.get(LinearInequalityPatternProcessorStatistics.MotzkinTransformationsApproxConstraints);

		mMotzkinCoefficientsNormalConstr += (Integer) linearInequalityStats
				.get(LinearInequalityPatternProcessorStatistics.MotzkinCoefficientsNormalConstraints);
		mMotzkinCoefficientsApproxConstr += (Integer) linearInequalityStats
				.get(LinearInequalityPatternProcessorStatistics.MotzkinCoefficientsApproxConstraints);

		mConstraintsSolvingTime +=
				(Long) linearInequalityStats.get(LinearInequalityPatternProcessorStatistics.ConstraintsSolvingTime);

		mConstraintsConstructionTime += (Long) linearInequalityStats
				.get(LinearInequalityPatternProcessorStatistics.ConstraintsConstructionTime);
		mSumNonUnsatCoreLocs += numOfNonUnsatCoreLocs;
		mSumNonUnsatCoreVars += numOfNonUnsatCoreVars;
		mSatStatus.count(satResult);
	}
}
