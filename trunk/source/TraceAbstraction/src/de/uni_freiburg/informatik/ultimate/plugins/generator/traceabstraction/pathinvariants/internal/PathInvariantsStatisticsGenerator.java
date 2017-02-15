package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.PathInvariantsGenerator.PathInvariantsStatisticsDefinitions;
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
	private int mDiffOfLiveVariables;
	private int mDiffOfUnsatCoreVars;
	
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
		mDiffOfLiveVariables = 0;
		mDiffOfUnsatCoreVars = 0;
	}


	@Override
	public Collection<String> getKeys() {
		return PathInvariantsStatisticsType.getInstance().getKeys();
	}

	@Override
	public Object getValue(final String key) {
		final PathInvariantsStatisticsDefinitions keyEnum = Enum.valueOf(PathInvariantsStatisticsDefinitions.class, key);
		switch (keyEnum) {
		case SumOfLocs: return mNumOfPathProgramLocations;
		case ProgramVars: return mNumOfVars;
		case SumOfTemplateInequalities: return mSumOfTemplateInequalities;
		case DiffOfLocsInUnsatCore: return mDiffOfLocsInUnsatCore;
		case DiffOfVarsInUnsatCore: return mDiffOfVarsInUnsatCore;
		case MaxNumOfInequalities: return mMaxNumOfInequalitiesPerRound;
		case MaxRound : return mMaxRound;
		case DAGSizeConstraints : return mDAGSizeSumOfConstraints;
		case VarsPerLoc: return mSumOfVarsPerLoc;
		case DiffLiveVarsPerLoc: return mDiffOfLiveVariables;
		case DiffUnsatCoreVars: return mDiffOfUnsatCoreVars;
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


	public void addStatisticsData(final int numOfTemplateInequalitiesForThisRound, final int sumOfVarsPerLoc, final int diffOfLiveVariables,
			final int diffOfUnsatCoreVars, final int DAGSizeSumOfConstraints, final int round) {
		if (numOfTemplateInequalitiesForThisRound > mMaxNumOfInequalitiesPerRound) {
			mMaxNumOfInequalitiesPerRound = numOfTemplateInequalitiesForThisRound;
		}
		mSumOfTemplateInequalities += numOfTemplateInequalitiesForThisRound;
		mDAGSizeSumOfConstraints += DAGSizeSumOfConstraints;
		mSumOfVarsPerLoc += sumOfVarsPerLoc;
		mDiffOfLiveVariables += diffOfLiveVariables;
		mDiffOfUnsatCoreVars += diffOfUnsatCoreVars;
		if (round > mMaxRound) {
			mMaxRound  = round;
		}
	}
	
	@Override
	public String toString() {
		return AStatisticsType.prettyprintBenchmarkData(getKeys(), PathInvariantsStatisticsDefinitions.class, this);
	}
}
