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

package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.evals;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ConversionContext;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.ultimatetest.suites.AbstractEvalTestSuite;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class PricedTimedAutomataTestSuite extends AbstractEvalTestSuite {

	private static final String[] BPL = new String[] { ".bpl" };
	private static final int DEFAULT_LIMIT = Integer.MAX_VALUE;

	// @formatter:off
	@SuppressWarnings("unchecked")
	private static final Triple<String, String[], String>[] TOOLCHAINS = new Triple[] {
//			new Triple<>("AutomizerBpl.xml", BPL, "automizer/PricedTimedAutomata/TreeInterpolation.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "automizer/PricedTimedAutomata/TreeInterpolation-Totalinterpolation.epf"),
			new Triple<>("AutomizerBpl.xml", BPL, "automizer/PricedTimedAutomata/TwoTrack-CNF.epf"),
			new Triple<>("AutomizerBpl.xml", BPL, "automizer/PricedTimedAutomata/TwoTrack-CNF+AI_OCT.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "automizer/PricedTimedAutomata/TwoTrack-Nolbe.epf"),

//			new Triple<>("AutomizerBpl.xml", BPL, "automizer/PricedTimedAutomata/TreeInterpolation+AI_OCT.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "automizer/PricedTimedAutomata/TreeInterpolation-Totalinterpolation+AI_OCT.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "automizer/PricedTimedAutomata/TwoTrack+AI_OCT.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "automizer/PricedTimedAutomata/TwoTrack-Nolbe+AI_OCT.epf"),
			
//			new Triple<>("AutomizerBpl.xml", BPL, "automizer/PricedTimedAutomata/TwoTrack-Mathsat.epf"),
			new Triple<>("AutomizerBpl.xml", BPL, "automizer/PricedTimedAutomata/CraigInterpolation-Z3.epf"),
			new Triple<>("AutomizerBpl.xml", BPL, "automizer/PricedTimedAutomata/CraigInterpolation-Z3+AI_OCT.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "automizer/PricedTimedAutomata/PricedTimedAutomata_z3.epf"),
	};



	private static final String[] INPUT = new String[] {
			"examples/programs/real-life/PricedTimedautomataBSearch/",
//			"examples/programs/real-life/PricedTimedAutomata/u2b06_batman_intermittent_no_power_SAFE.bpl",

	};

	// @formatter:on

	@Override
	protected long getTimeout() {
		return 3600 * 1000;
	}

	@Override
	protected ColumnDefinition[] getColumnDefinitions() {
		// @formatter:off
		return new ColumnDefinition[] {
				new ColumnDefinition(
						"Overall time", "Avg. runtime",
						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),	
				new ColumnDefinition(
						"Peak memory consumption (bytes)", "Mem{-}ory",
						ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average),						
				new ColumnDefinition(
						"Overall iterations", "Iter{-}ations",
						ConversionContext.Divide(1, 2, ""), Aggregate.Ignore, Aggregate.Average),

//				new ColumnDefinition("InterpolantConsolidationBenchmark_InterpolantsDropped", "Interpolants dropped", ConversionContext.Divide(1, 2, ""), Aggregate.Ignore, Aggregate.Average),								
//				new ColumnDefinition("InterpolantConsolidationBenchmark_NewlyCreatedInterpolants", "Newly Created Interpolants", ConversionContext.Divide(1, 2, ""), Aggregate.Ignore, Aggregate.Average),								
//				new ColumnDefinition("EdgeCheckerBenchmarkData_Sat", "Num Sats", ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),										
//				new ColumnDefinition("EdgeCheckerBenchmarkData_Unsat", "Num Unsats", ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),										
//				new ColumnDefinition("EdgeCheckerBenchmarkData_Unknown", "Num Unknown", ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Sum),										
//				new ColumnDefinition("EdgeCheckerBenchmarkData_NotChecked", "Num NotChecked", ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Sum),										
//				new ColumnDefinition("InterpolantConsolidationBenchmark_NumOfHoareTripleChecks", "NumOfHTC{-}Checks{-}IC", 
//						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Max),								
//				new ColumnDefinition("InterpolantConsolidationBenchmark_TimeOfConsolidation", "Time{-}Of{-}Consol.", 
//						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average)
				
//				new ColumnDefinition(
//						"NumberOfCodeBlocks", null,
//						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
//				new ColumnDefinition(
//						"NumberOfCodeBlocksAsserted", null,
//						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),		
//				new ColumnDefinition(
//						"SizeOfPredicatesFP", null,
//						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),	
//				new ColumnDefinition(
//						"SizeOfPredicatesBP", null,
//						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),	
//				new ColumnDefinition(
//						"Conjuncts in SSA", null,
//						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),	
//				new ColumnDefinition(
//						"Conjuncts in UnsatCore", null,
//						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
//				new ColumnDefinition(
//						"ICC %", "ICC",
//						ConversionContext.Percent(true,2), Aggregate.Ignore, Aggregate.Average)
				new ColumnDefinition("Minimization time", "mnmz time", 
						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("BasicInterpolantAutomatonTime", "bia time", 
						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("EdgeCheckerBenchmarkData_EdgeCheckerTime", "ec time", 
						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("PredicateUnifierData_Time", "pu time", 
						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("traceCheckBenchmark_InterpolantComputationTime", "itp time", 
						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("Automata difference", "adiff time", 
						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("Peak memory consumption (bytes)", "Peak Memory",
						ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average), };
		// @formatter:on
	}

	@Override
	public ITestResultDecider constructITestResultDecider(UltimateRunDefinition urd) {
		return new SafetyCheckTestResultDecider(urd, false);
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final Triple<String, String[], String> triple : TOOLCHAINS) {
			final DirectoryFileEndingsPair[] pairs = new DirectoryFileEndingsPair[INPUT.length];
			for (int i = 0; i < INPUT.length; ++i) {
				pairs[i] = new DirectoryFileEndingsPair(INPUT[i], triple.getSecond(), DEFAULT_LIMIT);
			}
			addTestCase(triple.getFirst(), triple.getThird(), pairs);
		}
		return super.createTestCases();
	}
}
