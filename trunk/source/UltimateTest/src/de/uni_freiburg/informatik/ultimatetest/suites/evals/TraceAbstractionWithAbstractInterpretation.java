/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Test Library.
 * 
 * The ULTIMATE Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Test Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Test Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimatetest.suites.evals;

import java.util.ArrayList;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.suites.AbstractEvalTestSuite;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimatetest.summaries.ComparativeSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.ConversionContext;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition.Aggregate;

public class TraceAbstractionWithAbstractInterpretation extends AbstractEvalTestSuite {

	private static final String[] FILEENDINGS = new String[] { ".c" };
	
	private static final DirectoryFileEndingsPair[] INPUT = new DirectoryFileEndingsPair[] { 
		getPair("examples/programs/regression/c/"), 
		getPair("examples/svcomp/locks/"),		
		//current bugs
		getPair("examples/programs/regression/c/NestedDeclarators.c"),
	};

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		addTestCases("AutomizerC.xml", "ai/Automizer+AI.epf", INPUT);
		addTestCases("AutomizerC.xml", "ai/Automizer+AI-Fast.epf", INPUT);
		addTestCases("AutomizerC.xml", "ai/Automizer.epf", INPUT);
		addTestCases("AbstractInterpretationC.xml", "AbsIntOrTASingle.epff", INPUT);
		return super.createTestCases();
	}
	
	@Override
	protected long getTimeout() {
		return 45 * 1000;
		// return 20 * 60 * 1000;
	}

	@Override
	protected ColumnDefinition[] getColumnDefinitions() {
		// @formatter:off
		return new ColumnDefinition[]{
				new ColumnDefinition(
						"Runtime (ns)", "Avg. runtime",
						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),	
				new ColumnDefinition(
						"Allocated memory end (bytes)", "Mem{-}ory",
						ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average),
			};
		// @formatter:on
	}


	private static DirectoryFileEndingsPair getPair(String directory, int limit) {
		return new DirectoryFileEndingsPair(directory, FILEENDINGS, limit);
	}

	private static DirectoryFileEndingsPair getPair(String directory) {
		return new DirectoryFileEndingsPair(directory, FILEENDINGS);
	}

	@Override
	protected ITestSummary[] constructTestSummaries() {
		ITestSummary[] summaries = super.constructTestSummaries();
		ArrayList<ITestSummary> rtr = new ArrayList<>();
		for (ITestSummary summary : summaries) {
			rtr.add(summary);
		}
		rtr.add(new ComparativeSummary(getClass()));
		return rtr.toArray(new ITestSummary[rtr.size()]);
	}

}
