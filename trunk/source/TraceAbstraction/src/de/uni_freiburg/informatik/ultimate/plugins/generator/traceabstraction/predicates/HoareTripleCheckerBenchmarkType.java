/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.Arrays;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.InCaReCounter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.IBenchmarkDataProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.IBenchmarkType;

public class HoareTripleCheckerBenchmarkType implements IBenchmarkType {
	
	private static HoareTripleCheckerBenchmarkType s_Instance = new HoareTripleCheckerBenchmarkType();
	public final static String s_SDtfs = "SDtfs";
	public final static String s_SDslu = "SDslu";
	public final static String s_SDs = "SDs";
	public final static String s_SdLazyCounter = "lazy";
	public final static String s_SolverCounterSat = "Sat";
	public final static String s_SolverCounterUnsat = "Unsat";
	public final static String s_SolverCounterUnknown = "Unknown";
	public final static String s_SolverCounterNotchecked = "NotChecked";
	public final static String s_EdgeCheckerTime = "EdgeCheckerTime";
	
	public static HoareTripleCheckerBenchmarkType getInstance() {
		return s_Instance;
	}
	
	@Override
	public Collection<String> getKeys() {
		return Arrays.asList(new String[] { s_SDtfs, s_SDslu, s_SDs, 
				s_SdLazyCounter, 
				s_SolverCounterSat, s_SolverCounterUnsat, 
				s_SolverCounterUnknown, s_SolverCounterNotchecked, s_EdgeCheckerTime });
	}
	
	@Override
	public Object aggregate(String key, Object value1, Object value2) {
		switch (key) {
		case s_SDtfs:
		case s_SDslu:
		case s_SDs:
		case s_SdLazyCounter:
		case s_SolverCounterSat: 
		case s_SolverCounterUnsat:
		case s_SolverCounterUnknown:
		case s_SolverCounterNotchecked:
			InCaReCounter resultInCaReCounter = (InCaReCounter) value1;
			InCaReCounter inCaReCounter2 = (InCaReCounter) value2;
			resultInCaReCounter.add(inCaReCounter2);
			return resultInCaReCounter;
		case s_EdgeCheckerTime:
			Long time1 = (Long) value1;
			Long time2 = (Long) value2;
			return time1 + time2;
		default:
			throw new AssertionError("unknown key");
		}
	}

	@Override
	public String prettyprintBenchmarkData(IBenchmarkDataProvider benchmarkData) {
		StringBuilder sb = new StringBuilder();
		sb.append("HoareTripleChecks: ");
		sb.append(benchmarkData.getValue(s_SDtfs) + " SDtfs, ");
		sb.append(benchmarkData.getValue(s_SDslu) + " SDslu, ");
		sb.append(benchmarkData.getValue(s_SDs) + " SDs, ");
		sb.append(benchmarkData.getValue(s_SdLazyCounter) + " lazy, ");
		sb.append(benchmarkData.getValue(s_SolverCounterSat) + " Sat,");
		sb.append(benchmarkData.getValue(s_SolverCounterUnsat) + " Unsat,");
		sb.append(benchmarkData.getValue(s_SolverCounterUnknown) + " Unknown,");
		sb.append(benchmarkData.getValue(s_SolverCounterNotchecked) + " NotChecked.");
		sb.append(" HoareTripleCheck time: ");
		long time = (long) benchmarkData.getValue(s_EdgeCheckerTime);
		sb.append(TraceAbstractionBenchmarks.prettyprintNanoseconds(time));
		return sb.toString();
	}

}
