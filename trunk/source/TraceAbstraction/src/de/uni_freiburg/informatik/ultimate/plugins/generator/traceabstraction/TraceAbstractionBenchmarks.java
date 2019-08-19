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

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

public class TraceAbstractionBenchmarks implements ICsvProviderProvider<Object> {
	
	private final StatisticsData mCegarLoopBenchmarkData;
	private final int mProcedures;
	private final int mLocations;
	private final int mErrorLocations;
	
	public TraceAbstractionBenchmarks(final IIcfg<?> rootAnnot) {
		mProcedures = rootAnnot.getProcedureEntryNodes().size();
		mLocations = (int) rootAnnot.getProgramPoints().entrySet().stream()
				.flatMap(a -> a.getValue().entrySet().stream()).count();
		mErrorLocations = (int) rootAnnot.getProcedureErrorNodes().entrySet().stream()
				.flatMap(a -> a.getValue().stream()).count();
		mCegarLoopBenchmarkData = new StatisticsData();
	}
	
	public void aggregateBenchmarkData(final CegarLoopStatisticsGenerator cegarLoopBenchmarkGenerator) {
		mCegarLoopBenchmarkData.aggregateBenchmarkData(cegarLoopBenchmarkGenerator);
	}
	
	public static String prettyprintNanoseconds(final long time) {
		final long seconds = time / 1000000000;
		final long tenthDigit = time / 100000000 % 10;
		return seconds + "." + tenthDigit + "s";
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("CFG has ");
		sb.append(mProcedures);
		sb.append(" procedures, ");
		sb.append(mLocations);
		sb.append(" locations, ");
		sb.append(mErrorLocations);
		sb.append(" error locations. ");
		sb.append(mCegarLoopBenchmarkData.toString());
		return sb.toString();
	}
	
	@Override
	public ICsvProvider<Object> createCsvProvider() {
		return mCegarLoopBenchmarkData.createCsvProvider();
	}
	
}
