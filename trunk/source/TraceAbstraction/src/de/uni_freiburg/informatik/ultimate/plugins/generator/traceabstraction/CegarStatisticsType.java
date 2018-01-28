/*
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

import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsType;

public class CegarStatisticsType extends StatisticsType<CegarLoopStatisticsDefinitions> {
	
	public static Function<Object, Function<Object,Object>> s_SizeIterationPairDataAggregation = 
			x -> y -> { return ((SizeIterationPair) x).getSize() >= ((SizeIterationPair) y).getSize() ? x : y; };
	
	public CegarStatisticsType() {
		super(CegarLoopStatisticsDefinitions.class);
	}

	private static CegarStatisticsType s_Instance = new CegarStatisticsType();
	
	public static CegarStatisticsType getInstance() {
		return s_Instance;
	}


	public static String prettyprintNanoseconds(final long time) {
		final long seconds = time / 1000000000;
		final long tenthDigit = (time / 100000000) % 10;
		return seconds + "." + tenthDigit + "s";
	}

	public static class SizeIterationPair {
		final int mSize;
		final int mIteration;

		public SizeIterationPair(final int size, final int iteration) {
			super();
			mSize = size;
			mIteration = iteration;
		}

		public int getSize() {
			return mSize;
		}

		public int getIteration() {
			return mIteration;
		}

		@Override
		public String toString() {
			return "size=" + mSize + "occurred in iteration=" + mIteration;
		}
	}
}
