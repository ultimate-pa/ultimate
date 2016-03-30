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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple;

import java.util.Collection;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.HoareTripleCheckerStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.util.Benchmark;
import de.uni_freiburg.informatik.ultimate.util.InCaReCounter;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;

public class HoareTripleCheckerStatisticsGenerator implements IStatisticsDataProvider {
	
	protected final InCaReCounter m_SDtfsCounter;
	protected final InCaReCounter m_SDsluCounter;
	protected final InCaReCounter m_SDsCounter;
	protected final InCaReCounter m_SdLazyCounter;
	protected final InCaReCounter m_SolverCounterSat;
	protected final InCaReCounter m_SolverCounterUnsat;
	protected final InCaReCounter m_SolverCounterUnknown;
	protected final InCaReCounter m_SolverCounterNotChecked;
	protected final Benchmark m_Benchmark;

	protected boolean m_Running = false;

	public HoareTripleCheckerStatisticsGenerator() {
		m_SDtfsCounter = new InCaReCounter();
		m_SDsluCounter = new InCaReCounter();
		m_SDsCounter = new InCaReCounter();
		m_SdLazyCounter = new InCaReCounter();
		m_SolverCounterSat = new InCaReCounter();
		m_SolverCounterUnsat = new InCaReCounter();
		m_SolverCounterUnknown = new InCaReCounter();
		m_SolverCounterNotChecked= new InCaReCounter();
		m_Benchmark = new Benchmark();
		m_Benchmark.register(String.valueOf(HoareTripleCheckerStatisticsDefinitions.EdgeCheckerTime));
	}

	public InCaReCounter getSDtfsCounter() {
		return m_SDtfsCounter;
	}
	public InCaReCounter getSDsluCounter() {
		return m_SDsluCounter;
	}
	public InCaReCounter getSDsCounter() {
		return m_SDsCounter;
	}
	public InCaReCounter getSdLazyCounter() {
		return m_SdLazyCounter;
	}
	public InCaReCounter getSolverCounterSat() {
		return m_SolverCounterSat;
	}
	public InCaReCounter getSolverCounterUnsat() {
		return m_SolverCounterUnsat;
	}
	public InCaReCounter getSolverCounterUnknown() {
		return m_SolverCounterUnknown;
	}
	public InCaReCounter getSolverCounterNotChecked() {
		return m_SolverCounterNotChecked;
	}
	public long getEdgeCheckerTime() {
		return (long) m_Benchmark.getElapsedTime(String.valueOf(HoareTripleCheckerStatisticsDefinitions.EdgeCheckerTime), TimeUnit.NANOSECONDS);
	}
	public void continueEdgeCheckerTime() {
		assert m_Running == false : "Timing already running";
		m_Running = true;
		m_Benchmark.unpause(String.valueOf(HoareTripleCheckerStatisticsDefinitions.EdgeCheckerTime));
	}
	public void stopEdgeCheckerTime() {
		assert m_Running == true : "Timing not running";
		m_Running = false;
		m_Benchmark.pause(String.valueOf(HoareTripleCheckerStatisticsDefinitions.EdgeCheckerTime));
	}
	@Override
	public Collection<String> getKeys() {
		return HoareTripleCheckerStatisticsType.getInstance().getKeys();
	}
	public Object getValue(String key) {
		HoareTripleCheckerStatisticsDefinitions keyEnum = Enum.valueOf(HoareTripleCheckerStatisticsDefinitions.class, key);
		switch (keyEnum) {
		case SDtfs:
			return m_SDtfsCounter;
		case SDslu:
			return m_SDsluCounter;
		case SDs:
			return m_SDsCounter;
		case SdLazy:
			return m_SdLazyCounter;
		case SolverSat: 
			return m_SolverCounterSat;
		case SolverUnsat:
			return m_SolverCounterUnsat;
		case SolverUnknown:
			return m_SolverCounterUnknown;
		case SolverNotchecked:
			return m_SolverCounterNotChecked;
		case EdgeCheckerTime:
			return getEdgeCheckerTime();
		default:
			throw new AssertionError("unknown key");
		}
	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return HoareTripleCheckerStatisticsType.getInstance();
	}

}
