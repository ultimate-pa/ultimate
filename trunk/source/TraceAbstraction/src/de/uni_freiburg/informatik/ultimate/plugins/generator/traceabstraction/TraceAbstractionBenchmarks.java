/*
 * Copyright (C) 2014-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

public class TraceAbstractionBenchmarks implements ICsvProviderProvider<Object> {

	private final StatisticsData m_CegarLoopBenchmarkData;
	private final int m_Procedures;
	private final int m_Locations;
	private final int m_ErrorLocations;

	public TraceAbstractionBenchmarks(RootAnnot rootAnnot) {
		m_Procedures = rootAnnot.getEntryNodes().size();
		m_Locations = rootAnnot.getNumberOfProgramPoints();
		m_ErrorLocations = rootAnnot.getNumberOfErrorNodes();
		m_CegarLoopBenchmarkData = new StatisticsData();
	}

	public void aggregateBenchmarkData(CegarLoopBenchmarkGenerator cegarLoopBenchmarkGenerator) {
		m_CegarLoopBenchmarkData.aggregateBenchmarkData(cegarLoopBenchmarkGenerator);
	}

	public static String prettyprintNanoseconds(long time) {
		long seconds = time / 1000000000;
		long tenthDigit = (time / 100000000) % 10;
		return seconds + "." + tenthDigit + "s";
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("CFG has ");
		sb.append(m_Procedures);
		sb.append(" procedures, ");
		sb.append(m_Locations);
		sb.append(" locations, ");
		sb.append(m_ErrorLocations);
		sb.append(" error locations. ");
		sb.append(m_CegarLoopBenchmarkData.toString());
		return sb.toString();
	}

	@Override
	public ICsvProvider<Object> createCvsProvider() {
		return m_CegarLoopBenchmarkData.createCvsProvider();
	}

}
