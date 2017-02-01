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
	private int mNumOfLocations = 0;
	private int mMaxNumOfInequalitiesPerRound = 0;
	private int mSumOfTemplateInequalities = 0;
	private int mNumOfVars;
	private int mDiffOfLocsInUnsatCore;
	private int mDiffOfVarsInUnsatCore;
	private int mMaxRound = 0;;

	public void setNumOfLocations(final int numOfLocations) {
		mNumOfLocations = numOfLocations;
	}
	
	public void setNumOfVars(final int numOfVars) {
		mNumOfVars = numOfVars;
	}

	public void addPathInvariantsData(final int numOfInequalities, final int sumOfTemplateInequalities) {
		if (numOfInequalities > mMaxNumOfInequalitiesPerRound) {
			mMaxNumOfInequalitiesPerRound = numOfInequalities;
		}
		mSumOfTemplateInequalities = mSumOfTemplateInequalities + sumOfTemplateInequalities;

	}

	@Override
	public Collection<String> getKeys() {
		return PathInvariantsStatisticsType.getInstance().getKeys();
	}

	@Override
	public Object getValue(String key) {
		final PathInvariantsStatisticsDefinitions keyEnum = Enum.valueOf(PathInvariantsStatisticsDefinitions.class, key);
		switch (keyEnum) {
		case SumOfLocs: return mNumOfLocations;
		case NumOfVars: return mNumOfVars;
		case SumOfTemplateInequalities: return mSumOfTemplateInequalities;
		case DiffOfLocsInUnsatCore: return mDiffOfLocsInUnsatCore;
		case DiffOfVarsInUnsatCore: return mDiffOfVarsInUnsatCore;
		case MaxNumOfInequalitiesPerRound: return mMaxNumOfInequalitiesPerRound;
		case MaxRound : return mMaxRound;
		default:
			throw new AssertionError("unknown key");
		}
	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return PathInvariantsStatisticsType.getInstance();
	}
	
	public void setLocationAndVariablesData(int diffOfLocsInUnsatCore, int diffVarsInUnsatCore) {
		mDiffOfLocsInUnsatCore += diffOfLocsInUnsatCore;
		mDiffOfVarsInUnsatCore += diffVarsInUnsatCore;
	}

	public void setRound(int round) {
		if (round > mMaxRound) {
			mMaxRound  = round;
		}
	}
}
