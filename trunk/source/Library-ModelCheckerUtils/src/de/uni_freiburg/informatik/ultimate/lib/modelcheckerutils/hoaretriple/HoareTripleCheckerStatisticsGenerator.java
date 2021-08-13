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
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.concurrent.TimeUnit;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.HoareTripleCheckerStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.util.InCaReCounter;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil.Reflected;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.KeyType;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsAggregator.Statistics;
import de.uni_freiburg.informatik.ultimate.util.statistics.TimeTracker;

public class HoareTripleCheckerStatisticsGenerator implements IStatisticsDataProvider {

	@Statistics(type = KeyType.IN_CA_RE_COUNTER)
	private final InCaReCounter mSDtfsCounter;

	@Statistics(type = KeyType.IN_CA_RE_COUNTER)
	private final InCaReCounter mSDsluCounter;

	@Statistics(type = KeyType.IN_CA_RE_COUNTER)
	private final InCaReCounter mSDsCounter;

	@Statistics(type = KeyType.IN_CA_RE_COUNTER)
	private final InCaReCounter mSdLazyCounter;

	@Statistics(type = KeyType.IN_CA_RE_COUNTER)
	private final InCaReCounter mSolverCounterSat;

	@Statistics(type = KeyType.IN_CA_RE_COUNTER)
	private final InCaReCounter mSolverCounterUnsat;

	@Statistics(type = KeyType.IN_CA_RE_COUNTER)
	private final InCaReCounter mSolverCounterUnknown;

	@Statistics(type = KeyType.IN_CA_RE_COUNTER)
	private final InCaReCounter mSolverCounterNotChecked;

	@Reflected(prettyName = "Time")
	@Statistics(type = KeyType.TT_TIMER)
	private final TimeTracker mTimer;

	@Statistics(type = KeyType.IN_CA_RE_COUNTER)
	private final InCaReCounter mProtectedPredicate;

	@Statistics(type = KeyType.IN_CA_RE_COUNTER)
	private final InCaReCounter mProtectedAction;

	private boolean mRunning;

	private final Map<String, Supplier<Object>> mStats;

	public HoareTripleCheckerStatisticsGenerator() {
		mProtectedPredicate = new InCaReCounter();
		mProtectedAction = new InCaReCounter();
		mSDtfsCounter = new InCaReCounter();
		mSDsluCounter = new InCaReCounter();
		mSDsCounter = new InCaReCounter();
		mSdLazyCounter = new InCaReCounter();
		mSolverCounterSat = new InCaReCounter();
		mSolverCounterUnsat = new InCaReCounter();
		mSolverCounterUnknown = new InCaReCounter();
		mSolverCounterNotChecked = new InCaReCounter();

		mTimer = new TimeTracker();
		mRunning = false;

		mStats = new LinkedHashMap<>();
		mStats.put(HoareTripleCheckerStatisticsDefinitions.ProAct.name(), this::getProtectedActionCounter);
		mStats.put(HoareTripleCheckerStatisticsDefinitions.ProPred.name(), this::getProtectedPredicateCounter);
		mStats.put(HoareTripleCheckerStatisticsDefinitions.SDtfs.name(), this::getSDtfsCounter);
		mStats.put(HoareTripleCheckerStatisticsDefinitions.SDslu.name(), this::getSDsluCounter);
		mStats.put(HoareTripleCheckerStatisticsDefinitions.SDs.name(), this::getSDsCounter);
		mStats.put(HoareTripleCheckerStatisticsDefinitions.SdLazy.name(), this::getSdLazyCounter);
		mStats.put(HoareTripleCheckerStatisticsDefinitions.SolverSat.name(), this::getSolverCounterSat);
		mStats.put(HoareTripleCheckerStatisticsDefinitions.SolverUnsat.name(), this::getSolverCounterUnsat);
		mStats.put(HoareTripleCheckerStatisticsDefinitions.SolverUnknown.name(), this::getSolverCounterUnknown);
		mStats.put(HoareTripleCheckerStatisticsDefinitions.SolverNotchecked.name(), this::getSolverCounterNotChecked);
		mStats.put(HoareTripleCheckerStatisticsDefinitions.Time.name(), this::getEdgeCheckerTime);
	}

	public InCaReCounter getProtectedPredicateCounter() {
		return mProtectedPredicate;
	}

	public InCaReCounter getProtectedActionCounter() {
		return mProtectedAction;
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
		return mTimer.elapsedTime(TimeUnit.NANOSECONDS);
	}

	public void continueEdgeCheckerTime() {
		assert !mRunning : "Timing already running";
		mRunning = true;
		mTimer.start();
	}

	public void stopEdgeCheckerTime() {
		assert mRunning : "Timing not running";
		mRunning = false;
		mTimer.stop();
	}

	@Override
	public Collection<String> getKeys() {
		return HoareTripleCheckerStatisticsType.getInstance().getKeys();
	}

	@Override
	public Object getValue(final String key) {
		final Supplier<Object> rtr = mStats.get(key);
		if (rtr == null) {
			throw new AssertionError("unknown key");
		}
		return rtr.get();
	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return HoareTripleCheckerStatisticsType.getInstance();
	}

	@Override
	public String toString() {
		return getBenchmarkType().prettyprintBenchmarkData(this);
		// final StringBuilder builder = new StringBuilder();
		// builder.append(getClass().getSimpleName());
		// builder.append(" [");
		// final Iterator<Entry<String, Supplier<Object>>> iter = mStats.entrySet().iterator();
		// while (iter.hasNext()) {
		// final Entry<String, Supplier<Object>> entry = iter.next();
		// builder.append(entry.getKey());
		// builder.append('=');
		// builder.append(entry.getValue().get());
		// if (iter.hasNext()) {
		// builder.append(", ");
		// }
		// }
		// builder.append(']');
		// return builder.toString();
	}

}
