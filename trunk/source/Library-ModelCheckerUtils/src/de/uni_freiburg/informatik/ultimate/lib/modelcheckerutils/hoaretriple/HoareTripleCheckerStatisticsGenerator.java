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

import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil.Reflected;
import de.uni_freiburg.informatik.ultimate.util.statistics.BaseStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.DefaultMeasureDefinitions;
import de.uni_freiburg.informatik.ultimate.util.statistics.measures.InCaReCounter;
import de.uni_freiburg.informatik.ultimate.util.statistics.measures.TimeTracker;

public class HoareTripleCheckerStatisticsGenerator extends BaseStatisticsDataProvider {

	public static final String SOLVER_COUNTER_SAT = "Sat";
	public static final String SOLVER_COUNTER_UNSAT = "Unsat";
	public static final String SOLVER_COUNTER_UNKNOWN = "Unknown";
	public static final String TIME_HTC = "HtcTime";

	@Statistics(type = DefaultMeasureDefinitions.IN_CA_RE_COUNTER)
	private final InCaReCounter mSDtfs;

	@Statistics(type = DefaultMeasureDefinitions.IN_CA_RE_COUNTER)
	private final InCaReCounter mSDslu;

	@Statistics(type = DefaultMeasureDefinitions.IN_CA_RE_COUNTER)
	private final InCaReCounter mSDs;

	@Statistics(type = DefaultMeasureDefinitions.IN_CA_RE_COUNTER)
	private final InCaReCounter mSDLazy;

	@Reflected(prettyName = SOLVER_COUNTER_SAT)
	@Statistics(type = DefaultMeasureDefinitions.IN_CA_RE_COUNTER)
	private final InCaReCounter mSolverCounterSat;

	@Reflected(prettyName = SOLVER_COUNTER_UNSAT)
	@Statistics(type = DefaultMeasureDefinitions.IN_CA_RE_COUNTER)
	private final InCaReCounter mSolverCounterUnsat;

	@Reflected(prettyName = SOLVER_COUNTER_UNKNOWN)
	@Statistics(type = DefaultMeasureDefinitions.IN_CA_RE_COUNTER)
	private final InCaReCounter mSolverCounterUnknown;

	@Reflected(prettyName = "NotChecked")
	@Statistics(type = DefaultMeasureDefinitions.IN_CA_RE_COUNTER)
	private final InCaReCounter mSolverCounterNotChecked;

	@Reflected(prettyName = TIME_HTC)
	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mHtcTime;

	@Statistics(type = DefaultMeasureDefinitions.IN_CA_RE_COUNTER)
	private final InCaReCounter mProtectedPredicates;

	@Statistics(type = DefaultMeasureDefinitions.IN_CA_RE_COUNTER)
	private final InCaReCounter mProtectedActions;

	public HoareTripleCheckerStatisticsGenerator(final IToolchainStorage storage) {
		super(storage);
		mProtectedPredicates = new InCaReCounter();
		mProtectedActions = new InCaReCounter();
		mSDtfs = new InCaReCounter();
		mSDslu = new InCaReCounter();
		mSDs = new InCaReCounter();
		mSDLazy = new InCaReCounter();
		mSolverCounterSat = new InCaReCounter();
		mSolverCounterUnsat = new InCaReCounter();
		mSolverCounterUnknown = new InCaReCounter();
		mSolverCounterNotChecked = new InCaReCounter();
		mHtcTime = new TimeTracker();
	}

	public InCaReCounter getProtectedPredicateCounter() {
		return mProtectedPredicates;
	}

	public InCaReCounter getProtectedActionCounter() {
		return mProtectedActions;
	}

	public InCaReCounter getSDtfsCounter() {
		return mSDtfs;
	}

	public InCaReCounter getSDsluCounter() {
		return mSDslu;
	}

	public InCaReCounter getSDsCounter() {
		return mSDs;
	}

	public InCaReCounter getSdLazyCounter() {
		return mSDLazy;
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
		return mHtcTime.elapsedTime(TimeUnit.NANOSECONDS);
	}

	public void continueEdgeCheckerTime() {
		assert !mHtcTime.isRunning() : "Timing already running";
		mHtcTime.start();
	}

	public void stopEdgeCheckerTime() {
		assert mHtcTime.isRunning() : "Timing not running";
		mHtcTime.stop();
	}

}
