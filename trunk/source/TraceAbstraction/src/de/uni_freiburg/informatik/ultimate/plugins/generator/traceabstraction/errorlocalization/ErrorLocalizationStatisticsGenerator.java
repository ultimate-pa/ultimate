/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorlocalization;

import java.util.Collection;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.util.statistics.Benchmark;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

public class ErrorLocalizationStatisticsGenerator implements IStatisticsDataProvider {
	
	private final Benchmark mBenchmark;
	private boolean mRunning = false;

	private boolean mSuccesfullyFinished;
	private int mIcfgEdges;
	private int mErrorEnforcingIcfgEdges;
	private int mErrorAdmittingIcfgEdges;
	private int mErrorIrrelevantIcfgEdges;
	private int mNumberOfBranches;
	private double mAngelicScore;
	private final StatisticsData mHoareTripleCheckerStatistics;

	public ErrorLocalizationStatisticsGenerator() {
		mBenchmark = new Benchmark();
		mBenchmark.register(String.valueOf(ErrorLocalizationStatisticsDefinitions.ErrorLocalizationTime));
		mHoareTripleCheckerStatistics = new StatisticsData();
	}

	public long getErrorLocalizationTime() {
		return (long) mBenchmark.getElapsedTime(String.valueOf(ErrorLocalizationStatisticsDefinitions.ErrorLocalizationTime), TimeUnit.NANOSECONDS);
	}
	public void continueErrorLocalizationTime() {
		assert !mRunning : "Timing already running";
		mRunning = true;
		mBenchmark.unpause(String.valueOf(ErrorLocalizationStatisticsDefinitions.ErrorLocalizationTime));
	}
	public void stopErrorLocalizationTime() {
		assert mRunning : "Timing not running";
		mRunning = false;
		mBenchmark.pause(String.valueOf(ErrorLocalizationStatisticsDefinitions.ErrorLocalizationTime));
	}
	
	public void reportSuccesfullyFinished() {
		if (mSuccesfullyFinished) {
			throw new IllegalStateException("already finished before");
		}
		mSuccesfullyFinished = true;
	}
	
	public void reportIcfgEdge() {
		mIcfgEdges++;
	}
	
	public void reportErrorEnforcingIcfgEdge() {
		mErrorEnforcingIcfgEdges++;
	}
	
	public void reportErrorAdmittingIcfgEdge() {
		mErrorAdmittingIcfgEdges++;
	}
	
	public void reportErrorIrrelevantIcfgEdge() {
		mErrorIrrelevantIcfgEdges++;
	}
	
	public void reportNumberOfBranches(int numberOfBranches) {
		mNumberOfBranches = numberOfBranches;
	}
	
	public void reportAngelicScore(double angelicScore) {
		mAngelicScore = angelicScore;
	}
	
	public void addHoareTripleCheckerStatistics(final HoareTripleCheckerStatisticsGenerator hoareTripleCheckerStatistics) {
		mHoareTripleCheckerStatistics.aggregateBenchmarkData(hoareTripleCheckerStatistics);
	}

	
	@Override
	public Collection<String> getKeys() {
		return ErrorLocalizationStatisticsType.getInstance().getKeys();
	}
	@Override
	public Object getValue(final String key) {
		final ErrorLocalizationStatisticsDefinitions keyEnum = Enum.valueOf(ErrorLocalizationStatisticsDefinitions.class, key);
		switch (keyEnum) {
		case ErrorAdmittingIcfgEdges:
			return mErrorAdmittingIcfgEdges;
		case ErrorEnforcingIcfgEdges:
			return mErrorEnforcingIcfgEdges;
		case ErrorIrrelevantIcfgEdges:
			return mErrorIrrelevantIcfgEdges;
		case NumberOfBranches:
			return mNumberOfBranches;
		case AngelicScore:
			return mAngelicScore;
		case ErrorLocalizationTime:
			return getErrorLocalizationTime();
		case HoareTripleCheckerStatistics:
			return mHoareTripleCheckerStatistics;
		case IcfgEdges:
			return mIcfgEdges;
		case SuccesfullyFinished:
			return mSuccesfullyFinished ? 1 : 0;
		default:
			throw new AssertionError("unknown key");
		}
	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return ErrorLocalizationStatisticsType.getInstance();
	}



}
