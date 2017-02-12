package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.Collection;
import java.util.HashSet;
//import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.PathInvariantsGenerator.PathInvariantsStatisticsDefinitions;
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
	public Object getValue(String key) {
		final PathInvariantsStatisticsDefinitions keyEnum = Enum.valueOf(PathInvariantsStatisticsDefinitions.class, key);
		switch (keyEnum) {
		case SUM_OF_LOCS: return mNumOfPathProgramLocations;
		case PROGRAM_VARS: return mNumOfVars;
		case SUM_OF_TEMPLATE_INEQUALITIES: return mSumOfTemplateInequalities;
		case DIFF_OF_LOCS_IN_UNSAT_CORE: return mDiffOfLocsInUnsatCore;
		case DIFF_OF_VARS_IN_UNSAT_CORE: return mDiffOfVarsInUnsatCore;
		case MAX_NUM_OF_INEQUALITIES: return mMaxNumOfInequalitiesPerRound;
		case MAX_ROUND : return mMaxRound;
		case DAG_SIZE_CONSTRAINTS : return mDAGSizeSumOfConstraints;
		case VARS_PER_LOC: return mSumOfVarsPerLoc;
		case DIFF_LIVE_VARS_PER_LOC: return mDiffOfLiveVariables;
		case DIFF_UNSAT_CORE_VARS: return mDiffOfUnsatCoreVars;
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

	
	public void setLocationAndVariablesData(int diffOfLocsInUnsatCore, int diffVarsInUnsatCore) {
		mDiffOfLocsInUnsatCore += diffOfLocsInUnsatCore;
		mDiffOfVarsInUnsatCore += diffVarsInUnsatCore;
	}


	public void addStatisticsData(final int numOfTemplateInequalitiesForThisRound, int sumOfVarsPerLoc, int diffOfLiveVariables,
			int diffOfUnsatCoreVars, int DAGSizeSumOfConstraints, int round) {
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
}
