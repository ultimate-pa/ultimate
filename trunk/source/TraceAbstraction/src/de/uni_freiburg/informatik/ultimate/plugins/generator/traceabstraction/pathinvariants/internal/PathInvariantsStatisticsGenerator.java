package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.Collection;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.PathInvariantsGenerator.PathInvariantsStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.LinearInequalityInvariantPatternProcessor.LinearInequalityPatternProcessorStatistics;
import de.uni_freiburg.informatik.ultimate.util.statistics.AStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;

public class PathInvariantsStatisticsGenerator implements IStatisticsDataProvider {
	private int mNumOfPathProgramLocations;
	private int mMaxNumOfInequalitiesPerRound;
	private int mSumOfTemplateInequalities;
	private int mNumOfVars;
	private int mDiffOfLocsInUnsatCore;
	private int mDiffOfVarsInUnsatCore;
	private int mMaxRound; 
	private int mDAGSizeSumOfConstraints;
	private int mSumOfVarsPerLoc;
	private int mNumOfNonLiveVariables;
	private int mNumOfNonUnsatCoreVars;
	private int mMinNumOfInequalitiesOfMostRecentRound;
	private int mProgramSize;
	private int mSizeOfLargestTemplate;
	private int mSizeOfSmallestTemplate;
	private int mMotzkinTransformations;
	private String mSatStatus;
	
	public void initializeStatistics() {
		mNumOfPathProgramLocations = 0;
		mMaxNumOfInequalitiesPerRound = 0;
		mSumOfTemplateInequalities = 0;
		mNumOfVars = 0;
		mDiffOfLocsInUnsatCore = 0; 
		mDiffOfVarsInUnsatCore = 0;
		mMaxRound = 0;
		mDAGSizeSumOfConstraints = 0;
		mSumOfVarsPerLoc = 0;
		mNumOfNonLiveVariables = 0;
		mNumOfNonUnsatCoreVars = 0;
		mMinNumOfInequalitiesOfMostRecentRound = 0;
		mProgramSize = 0;
		mSizeOfLargestTemplate = 0;
		mSizeOfSmallestTemplate = 0;
		mMotzkinTransformations = 0;
		mSatStatus = "";
	}


	@Override
	public Collection<String> getKeys() {
		return PathInvariantsStatisticsType.getInstance().getKeys();
	}

	@Override
	public Object getValue(final String key) {
		final PathInvariantsStatisticsDefinitions keyEnum = Enum.valueOf(PathInvariantsStatisticsDefinitions.class, key);
		switch (keyEnum) {
		case ProgramLocs: return mNumOfPathProgramLocations;
		case ProgramSize: return mProgramSize;
		case ProgramVars: return mNumOfVars;
		case DiffOfLocsInUnsatCore: return mDiffOfLocsInUnsatCore;
		case DiffOfVarsInUnsatCore: return mDiffOfVarsInUnsatCore;
		case SumOfTemplateInequalities: return mSumOfTemplateInequalities;
		case SizeOfLargestTemplate: return mSizeOfLargestTemplate;
		case SizeOfSmallestTemplate: return mSizeOfSmallestTemplate;
		case MaxNumOfInequalities: return mMaxNumOfInequalitiesPerRound;
		case MaxRound : return mMaxRound;
		case DAGSizeConstraints : return mDAGSizeSumOfConstraints;
		case SumVarsPerLoc: return mSumOfVarsPerLoc;
		case SumNonLiveVarsPerLoc: return mNumOfNonLiveVariables;
		case SumNonUnsatCoreVars: return mNumOfNonUnsatCoreVars;
		case MotzkinTransformations: return mMotzkinTransformations;
		case SatStatus: return mSatStatus;
		default:
			throw new AssertionError("unknown key");
		}
	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return PathInvariantsStatisticsType.getInstance();
	}

	public void setNumOfPathProgramLocations(final int numOfLocations) {
		mNumOfPathProgramLocations = numOfLocations;
	}
	
	public void setNumOfVars(final int numOfVars) {
		mNumOfVars = numOfVars;
	}

	
	public void setLocationAndVariablesData(final int diffOfLocsInUnsatCore, final int diffVarsInUnsatCore) {
		mDiffOfLocsInUnsatCore += diffOfLocsInUnsatCore;
		mDiffOfVarsInUnsatCore += diffVarsInUnsatCore;
	}


	public void addStatisticsData(final int numOfTemplateInequalitiesForThisRound, final int maximalTemplateSizeOfThisRound, final int minimalTemplateSizeOfThisRound, final int sumOfVarsPerLoc, final int numfOfNonLiveVariables,
			final int numOfNonUnsatCoreVars, Map<LinearInequalityPatternProcessorStatistics, Integer> linearInequalityStats, final int round,
			String satResult) {
		if (numOfTemplateInequalitiesForThisRound > mMaxNumOfInequalitiesPerRound) {
			mMaxNumOfInequalitiesPerRound = numOfTemplateInequalitiesForThisRound;
		}
		mMinNumOfInequalitiesOfMostRecentRound = minimalTemplateSizeOfThisRound;
		mSumOfTemplateInequalities += numOfTemplateInequalitiesForThisRound;
		mDAGSizeSumOfConstraints += linearInequalityStats.get(LinearInequalityPatternProcessorStatistics.DAGTreesizeOfConstraints);
		mSumOfVarsPerLoc += sumOfVarsPerLoc;
		mNumOfNonLiveVariables += numfOfNonLiveVariables;
		mNumOfNonUnsatCoreVars += numOfNonUnsatCoreVars;
		if (round > mMaxRound) {
			mMaxRound  = round;
		}
		mProgramSize = linearInequalityStats.get(LinearInequalityPatternProcessorStatistics.ProgramSize);
		if (maximalTemplateSizeOfThisRound > mSizeOfLargestTemplate) {
			mSizeOfLargestTemplate = maximalTemplateSizeOfThisRound;
		}
		mSizeOfSmallestTemplate = minimalTemplateSizeOfThisRound;
		mMotzkinTransformations += linearInequalityStats.get(LinearInequalityPatternProcessorStatistics.MotzkinTransformations);
		if (mSatStatus == "") {
			mSatStatus = satResult;
		} else {
			mSatStatus = mSatStatus + ", " + satResult;
		}
		
	}
	
	@Override
	public String toString() {
		return AStatisticsType.prettyprintBenchmarkData(getKeys(), PathInvariantsStatisticsDefinitions.class, this);
	}
}
