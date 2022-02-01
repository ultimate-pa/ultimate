/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple;

import java.util.Collection;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.HoareTripleCheckerStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.util.InCaReCounter;
import de.uni_freiburg.informatik.ultimate.util.statistics.Benchmark;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;

public class HoareTripleCheckerStatisticsGenerator implements IStatisticsDataProvider {
	
	protected final InCaReCounter mSDtfsCounter;
	protected final InCaReCounter mSDsluCounter;
	protected final InCaReCounter mSDsCounter;
	protected final InCaReCounter mSdLazyCounter;
	protected final InCaReCounter mSolverCounterSat;
	protected final InCaReCounter mSolverCounterUnsat;
	protected final InCaReCounter mSolverCounterUnknown;
	protected final InCaReCounter mSolverCounterNotChecked;
	protected final Benchmark mBenchmark;

	protected boolean mRunning = false;

	public HoareTripleCheckerStatisticsGenerator() {
		mSDtfsCounter = new InCaReCounter();
		mSDsluCounter = new InCaReCounter();
		mSDsCounter = new InCaReCounter();
		mSdLazyCounter = new InCaReCounter();
		mSolverCounterSat = new InCaReCounter();
		mSolverCounterUnsat = new InCaReCounter();
		mSolverCounterUnknown = new InCaReCounter();
		mSolverCounterNotChecked= new InCaReCounter();
		mBenchmark = new Benchmark();
		mBenchmark.register(String.valueOf(HoareTripleCheckerStatisticsDefinitions.Time));
	}

	public InCaReCounter getSDtfsCounter() {
		return mSDtfsCounter;
	}
	public InCaReCounter getSDsluCounter() {
		return mSDsluCounter;
	}
	public InCaReCounter getSDsCounter() {
		return mSDsCounter;
	}
	public InCaReCounter getSdLazyCounter() {
		return mSdLazyCounter;
	}
	public InCaReCounter getSolverCounterSat() {
		return mSolverCounterSat;
	}
	public InCaReCounter getSolverCounterUnsat() {
		return mSolverCounterUnsat;
	}
	public InCaReCounter getSolverCounterUnknown() {
		return mSolverCounterUnknown;
	}
	public InCaReCounter getSolverCounterNotChecked() {
		return mSolverCounterNotChecked;
	}
	public long getEdgeCheckerTime() {
		return (long) mBenchmark.getElapsedTime(String.valueOf(HoareTripleCheckerStatisticsDefinitions.Time), TimeUnit.NANOSECONDS);
	}
	public void continueEdgeCheckerTime() {
		assert !mRunning : "Timing already running";
		mRunning = true;
		mBenchmark.unpause(String.valueOf(HoareTripleCheckerStatisticsDefinitions.Time));
	}
	public void stopEdgeCheckerTime() {
		assert mRunning : "Timing not running";
		mRunning = false;
		mBenchmark.pause(String.valueOf(HoareTripleCheckerStatisticsDefinitions.Time));
	}
	@Override
	public Collection<String> getKeys() {
		return HoareTripleCheckerStatisticsType.getInstance().getKeys();
	}
	@Override
	public Object getValue(final String key) {
		final HoareTripleCheckerStatisticsDefinitions keyEnum = Enum.valueOf(HoareTripleCheckerStatisticsDefinitions.class, key);
		switch (keyEnum) {
		case SDtfs:
			return mSDtfsCounter;
		case SDslu:
			return mSDsluCounter;
		case SDs:
			return mSDsCounter;
		case SdLazy:
			return mSdLazyCounter;
		case SolverSat:
			return mSolverCounterSat;
		case SolverUnsat:
			return mSolverCounterUnsat;
		case SolverUnknown:
			return mSolverCounterUnknown;
		case SolverNotchecked:
			return mSolverCounterNotChecked;
		case Time:
			return getEdgeCheckerTime();
		default:
			throw new AssertionError("unknown key");
		}
	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return HoareTripleCheckerStatisticsType.getInstance();
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append("HoareTripleCheckerStatisticsGenerator [mSDtfsCounter=");
		builder.append(mSDtfsCounter);
		builder.append(", mSDsluCounter=");
		builder.append(mSDsluCounter);
		builder.append(", mSDsCounter=");
		builder.append(mSDsCounter);
		builder.append(", mSdLazyCounter=");
		builder.append(mSdLazyCounter);
		builder.append(", mSolverCounterSat=");
		builder.append(mSolverCounterSat);
		builder.append(", mSolverCounterUnsat=");
		builder.append(mSolverCounterUnsat);
		builder.append(", mSolverCounterUnknown=");
		builder.append(mSolverCounterUnknown);
		builder.append(", mSolverCounterNotChecked=");
		builder.append(mSolverCounterNotChecked);
		builder.append("]");
		return builder.toString();
	}
	
	

}
