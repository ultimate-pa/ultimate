/*
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.petrinetlbe;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.CachedIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.LiptonReductionStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.independencerelation.SemanticIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.independencerelation.SyntacticIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

public class PetriNetLargeBlockEncodingStatisticsGenerator implements IStatisticsDataProvider {

	private long mVarBasedMoverChecksPositive;
	private long mVarBasedMoverChecksNegative;
	private long mSemBasedMoverChecksPositive;
	private long mSemBasedMoverChecksNegative;
	private long mSemBasedMoverChecksUnknown;
	private long mSemBasedMoverCheckTime;
	private long mCheckedPairsTotal;
	private final StatisticsData mLiptonStatistics = new StatisticsData();

	public void reportCheckedPairsTotal(final int i) {
		mCheckedPairsTotal += i;
	}

	public void extractStatistics(final SemanticIndependenceRelation<?> semanticBasedCheck) {
		if (semanticBasedCheck != null) {
			mSemBasedMoverChecksPositive = semanticBasedCheck.getPositiveQueries();
			mSemBasedMoverChecksNegative = semanticBasedCheck.getNegativeQueries();
			mSemBasedMoverChecksUnknown = semanticBasedCheck.getUnknownQueries();
			mSemBasedMoverCheckTime = semanticBasedCheck.getComputationTimeNano();
		}
	}

	public void extractStatistics(final SyntacticIndependenceRelation<?, ?> variableBasedCheck) {
		mVarBasedMoverChecksPositive = variableBasedCheck.getPositiveQueries();
		mVarBasedMoverChecksNegative = variableBasedCheck.getNegativeQueries();
	}

	public void extractStatistics(final CachedIndependenceRelation<?, ?> cachedCheck) {
		mCheckedPairsTotal += cachedCheck.getPositiveCacheSize();
		mCheckedPairsTotal += cachedCheck.getNegativeCacheSize();
	}

	public void addLiptonStatistics(final LiptonReductionStatisticsGenerator stat) {
		mLiptonStatistics.aggregateBenchmarkData(stat);
	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return PetriNetLargeBlockEncodingStatisticsType.getInstance();
	}

	@Override
	public Object getValue(final String key) {
		final PetriNetLargeBlockEncodingStatisticsDefinitions keyEnum =
				Enum.valueOf(PetriNetLargeBlockEncodingStatisticsDefinitions.class, key);
		switch (keyEnum) {
		case VarBasedMoverChecksPositive:
			return mVarBasedMoverChecksPositive;
		case VarBasedMoverChecksNegative:
			return mVarBasedMoverChecksNegative;
		case SemBasedMoverChecksNegative:
			return mSemBasedMoverChecksNegative;
		case SemBasedMoverChecksPositive:
			return mSemBasedMoverChecksPositive;
		case SemBasedMoverChecksUnknown:
			return mSemBasedMoverChecksUnknown;
		case SemBasedMoverCheckTime:
			return mSemBasedMoverCheckTime;
		case CheckedPairsTotal:
			return mCheckedPairsTotal;
		case LiptonReductionStatistics:
			return mLiptonStatistics;
		default:
			throw new AssertionError("unknown data");
		}
	}

	@Override
	public Collection<String> getKeys() {
		return PetriNetLargeBlockEncodingStatisticsType.getInstance().getKeys();
	}

}