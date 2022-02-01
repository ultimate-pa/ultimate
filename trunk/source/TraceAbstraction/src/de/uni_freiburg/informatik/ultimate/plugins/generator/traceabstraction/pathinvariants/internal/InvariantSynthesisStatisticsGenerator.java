package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.Collection;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.PathInvariantsGenerator.InvariantSynthesisStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.LinearInequalityInvariantPatternProcessor.LinearInequalityPatternProcessorStatistics;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsType;

public class InvariantSynthesisStatisticsGenerator implements IStatisticsDataProvider {
	private int mNumOfPathProgramLocations;
	private int mNumOfPathProgramLocationsAfterLbe;
	private int mMaxNumOfInequalitiesPerRound;
	private int mNumOfPathProgramVars;

	private int mMaxRound;

	private int mTreeSizeSumOfNormalConstraints;
	private int mTreeSizeSumOfApproxConstraints;

	private int mSumOfVarsPerLoc;
	private int mNumOfNonLiveVariables;
	private int mNumOfNonUnsatCoreVars;
	private int mNumOfNonUnsatCoreLocs;
	private int mProgramSizeConjuncts;
	private int mSizeOfLargestTemplate;
	private int mSizeOfSmallestTemplate;

	private int mMotzkinTransformationsForNormalConstr;
	private int mMotzkinTransformationsForApproxConstr;

	private int mMotzkinCoefficientsNormalConstr;
	private int mMotzkinCoefficientsApproxConstr;

	private String mSatStatus;
	private int mSumOfTemplateInequalities;
	private long mConstraintsConstructionTime;
	private long mConstraintsSolvingTime;
	private Integer mProgramSizeDisjuncts;

	public void initializeStatistics() {
		mNumOfPathProgramLocations = 0;
		mNumOfPathProgramLocationsAfterLbe = 0;
		mMaxNumOfInequalitiesPerRound = 0;
		mNumOfPathProgramVars = 0;
		mNumOfNonUnsatCoreLocs = 0;
		mMaxRound = 0;
		mSumOfVarsPerLoc = 0;
		mNumOfNonLiveVariables = 0;
		mNumOfNonUnsatCoreVars = 0;
		mProgramSizeConjuncts = 0;
		mProgramSizeDisjuncts = 0;
		mSizeOfLargestTemplate = 0;
		mSizeOfSmallestTemplate = 0;
		mSumOfTemplateInequalities = 0;
		mTreeSizeSumOfNormalConstraints = 0;
		mTreeSizeSumOfApproxConstraints = 0;
		mMotzkinTransformationsForNormalConstr = 0;
		mMotzkinTransformationsForApproxConstr = 0;
		mMotzkinCoefficientsNormalConstr = 0;
		mMotzkinCoefficientsApproxConstr = 0;

		mSatStatus = "";
		mConstraintsConstructionTime = 0;
		mConstraintsSolvingTime = 0;
	}


	@Override
	public Collection<String> getKeys() {
		return InvariantSynthesisStatisticsType.getInstance().getKeys();
	}

	@Override
	public Object getValue(final String key) {
		final InvariantSynthesisStatisticsDefinitions keyEnum = Enum.valueOf(InvariantSynthesisStatisticsDefinitions.class, key);
		switch (keyEnum) {
		case ProgramSizeConjuncts: return mProgramSizeConjuncts;
		case ProgramSizeDisjuncts: return mProgramSizeDisjuncts;
		case ProgramLocs: return mNumOfPathProgramLocations;
		case ProgramLocsLbe: return mNumOfPathProgramLocationsAfterLbe;
		case ProgramVars: return mNumOfPathProgramVars;
		case SumOfTemplateInequalities : return mSumOfTemplateInequalities;
		case SizeOfLargestTemplate: return mSizeOfLargestTemplate;
		case SizeOfSmallestTemplate: return mSizeOfSmallestTemplate;
		case MaxNumOfInequalities: return mMaxNumOfInequalitiesPerRound;
		case MaxRound : return mMaxRound;
		case TreeSizeNormalConstr : return mTreeSizeSumOfNormalConstraints;
		case TreeSizeApproxConstr : return mTreeSizeSumOfApproxConstraints;
		case SumVarsPerLoc: return mSumOfVarsPerLoc;
		case SumNonLiveVarsPerLoc: return mNumOfNonLiveVariables;
		case SumNonUnsatCoreLocs: return mNumOfNonUnsatCoreLocs;
		case SumNonUnsatCoreVars: return mNumOfNonUnsatCoreVars;
		case MotzkinTransformationsNormalConstr: return mMotzkinTransformationsForNormalConstr;
		case MotzkinTransformationsApproxConstr: return mMotzkinTransformationsForApproxConstr;
		case MotzkinCoefficientsNormalConstr: return mMotzkinCoefficientsNormalConstr;
		case MotzkinCoefficientsApproxConstr : return mMotzkinCoefficientsApproxConstr;
		case ConstraintsSolvingTime: return mConstraintsSolvingTime;
		case ConstraintsConstructionTime : return mConstraintsConstructionTime;
		case SatStatus: return mSatStatus;
		default:
			throw new AssertionError("unknown key");
		}
	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return InvariantSynthesisStatisticsType.getInstance();
	}

	public void setNumOfPathProgramLocations(final int numOfLocsBeforeLbe, final int numOfLocsAfterLbe) {
		mNumOfPathProgramLocations = numOfLocsBeforeLbe;
		mNumOfPathProgramLocationsAfterLbe = numOfLocsAfterLbe;

	}

	public void setNumOfVars(final int numOfVars) {
		mNumOfPathProgramVars = numOfVars;
	}


	public void addStatisticsDataBeforeCheckSat(final int numOfTemplateInequalitiesForThisRound, final int maximalTemplateSizeOfThisRound,
			final int minimalTemplateSizeOfThisRound, final int sumOfVarsPerLoc, final int numfOfNonLiveVariables, final int round) {
		if (numOfTemplateInequalitiesForThisRound > mMaxNumOfInequalitiesPerRound) {
			mMaxNumOfInequalitiesPerRound = numOfTemplateInequalitiesForThisRound;
		}
		mSumOfTemplateInequalities += numOfTemplateInequalitiesForThisRound;
		mSumOfVarsPerLoc += sumOfVarsPerLoc;
		mNumOfNonLiveVariables += numfOfNonLiveVariables;
		if (round > mMaxRound) {
			mMaxRound  = round;
		}
		if (maximalTemplateSizeOfThisRound > mSizeOfLargestTemplate) {
			mSizeOfLargestTemplate = maximalTemplateSizeOfThisRound;
		}
		mSizeOfSmallestTemplate = minimalTemplateSizeOfThisRound;
	}

	public void addStatisticsDataAfterCheckSat(final int numOfNonUnsatCoreLocs, final int numOfNonUnsatCoreVars, final String satResult,
			final Map<LinearInequalityPatternProcessorStatistics, Object> linearInequalityStats) {
		mProgramSizeConjuncts = (Integer)linearInequalityStats.get(LinearInequalityPatternProcessorStatistics.ProgramSizeConjuncts);
		mProgramSizeDisjuncts = (Integer)linearInequalityStats.get(LinearInequalityPatternProcessorStatistics.ProgramSizeDisjuncts);

		mTreeSizeSumOfNormalConstraints += (Integer)linearInequalityStats.get(LinearInequalityPatternProcessorStatistics.TreesizeNormalConstraints);
		mTreeSizeSumOfApproxConstraints += (Integer)linearInequalityStats.get(LinearInequalityPatternProcessorStatistics.TreesizeApproxConstraints);

		mMotzkinTransformationsForNormalConstr += (Integer)linearInequalityStats.get(LinearInequalityPatternProcessorStatistics.MotzkinTransformationsNormalConstraints);
		mMotzkinTransformationsForApproxConstr += (Integer)linearInequalityStats.get(LinearInequalityPatternProcessorStatistics.MotzkinTransformationsApproxConstraints);

		mMotzkinCoefficientsNormalConstr += (Integer)linearInequalityStats.get(LinearInequalityPatternProcessorStatistics.MotzkinCoefficientsNormalConstraints);
		mMotzkinCoefficientsApproxConstr += (Integer)linearInequalityStats.get(LinearInequalityPatternProcessorStatistics.MotzkinCoefficientsApproxConstraints);

		mConstraintsSolvingTime += (Long)linearInequalityStats.get(LinearInequalityPatternProcessorStatistics.ConstraintsSolvingTime);

		mConstraintsConstructionTime += (Long)linearInequalityStats.get(LinearInequalityPatternProcessorStatistics.ConstraintsConstructionTime);
		mNumOfNonUnsatCoreLocs += numOfNonUnsatCoreLocs;
		mNumOfNonUnsatCoreVars += numOfNonUnsatCoreVars;
		if (mSatStatus == "") {
			mSatStatus = satResult;
		} else {
			mSatStatus = mSatStatus + ", " + satResult;
		}

	}

	@Override
	public String toString() {
		return StatisticsType.prettyprintBenchmarkData(getKeys(), InvariantSynthesisStatisticsDefinitions.class, this);
	}
}
