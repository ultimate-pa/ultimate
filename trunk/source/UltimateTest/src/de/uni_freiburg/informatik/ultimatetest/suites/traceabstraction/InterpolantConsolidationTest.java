package de.uni_freiburg.informatik.ultimatetest.suites.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.util.Benchmark;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.reporting.CsvConcatenator;
import de.uni_freiburg.informatik.ultimatetest.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.suites.AbstractModelCheckerTestSuite.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimatetest.summaries.ConversionContext;
import de.uni_freiburg.informatik.ultimatetest.summaries.KingOfTheHillSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.LatexOverviewSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.StandingsSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.TraceAbstractionTestSummary;

/**
 * 
 * @author Betim Musa <musab@informatik.uni-freiburg.de>, Matthias Heizmann
 *
 */
public class InterpolantConsolidationTest extends AbstractTraceAbstractionTestSuite {
	
//	private static int m_FilesPerDirectoryLimit = Integer.MAX_VALUE;
	private static int m_FilesPerDirectoryLimit = 5;
	
	private static final DirectoryFileEndingsPair[] m_SVCOMP_Examples = {
//		/*** Category 1. Arrays ***/
//		new DirectoryFileEndingsPair("examples/svcomp/array-examples/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
//		
//		/*** Category 2. Bit Vectors ***/
//		new DirectoryFileEndingsPair("examples/svcomp/bitvector/", new String[]{ ".i", ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/bitvector-regression/", new String[]{ ".i", ".c" }, m_FilesPerDirectoryLimit) ,
//		
//		/*** Category 4. Control Flow and Integer Variables ***/
//		new DirectoryFileEndingsPair("examples/svcomp/ntdrivers-simplified/", new String[]{".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ssh-simplified/", new String[]{".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/locks/", new String[]{".c" }, m_FilesPerDirectoryLimit) ,
//		
//		new DirectoryFileEndingsPair("examples/svcomp/loops/", new String[]{".i"}, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/loop-acceleration/", new String[]{".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/loop-invgen/", new String[]{".i"}, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/loop-lit/", new String[]{ ".i", ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/loop-new/", new String[]{".i"}, m_FilesPerDirectoryLimit) ,
//		
//		new DirectoryFileEndingsPair("examples/svcomp/eca-rers2012/", new String[]{".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/product-lines/", new String[]{".c" }, m_FilesPerDirectoryLimit) ,
//		
//		/*** Category 5. Device Drivers Linux 64-bit ***/
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.0/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.4-simple/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.7.3/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-commit-tester/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-consumption/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.12-rc1/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.16-rc1/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-validator-v0.6/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		
//		/*** Category 6. Heap Manipulation / Dynamic Data Structures ***/
//		new DirectoryFileEndingsPair("examples/svcomp/heap-manipulation/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/list-properties/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-regression/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ddv-machzwd/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
//		
//		/*** Category 7. Memory Safety ***/
//		new DirectoryFileEndingsPair("examples/svcomp/memsafety/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/memory-alloca/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/memory-unsafe/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
//
//		/*** Category 8. Recursive ***/
//		new DirectoryFileEndingsPair("examples/svcomp/recursive/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		
//		/*** Category 9. Sequentialized Concurrent Programs ***/
//		new DirectoryFileEndingsPair("examples/svcomp/systemc/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/seq-mthreaded/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/seq-pthread/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
//		
//		/*** Category 10. Simple  ***/
//		new DirectoryFileEndingsPair("examples/svcomp/ntdrivers/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ssh/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		
//		/*** Category 12. Termination ***/
//		new DirectoryFileEndingsPair("examples/svcomp/termination-crafted/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/termination-crafted-lit/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/termination-memory-alloca/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/termination-numeric/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
	};
	
	
	private static final String[] m_UltimateRepository = {
//		"examples/programs/regression",
//		"examples/programs/quantifier",
//		"examples/programs/recursivePrograms",
//		"examples/programs/toy",
	};


	
	/**
	 * List of path to setting files. 
	 * Ultimate will run on each program with each setting that is defined here.
	 * The path are defined relative to the folder "trunk/examples/settings/",
	 * because we assume that all settings files are in this folder.
	 * 
	 */
	private static final String[] m_Settings = {
			"automizer/interpolantConsolidation/FP.epf",
			"automizer/interpolantConsolidation/FP_CO.epf",
			"automizer/interpolantConsolidation/BP.epf",
			"automizer/interpolantConsolidation/BP_CO.epf",
			"automizer/interpolantConsolidation/TwoTrack_CO.epf",
			"automizer/interpolantConsolidation/TwoTrack.epf"
	};
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 60 * 1000;
	}
	
	private static final String[] m_BoogieToolchains = {
//		"AutomizerBpl.xml",
		"AutomizerBplInline.xml",
	};
	
	private static final String[] m_CToolchains = {
//		"AutomizerC.xml",
		"AutomizerCInline.xml",
	};

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (String setting : m_Settings) {
			for (String toolchain : m_CToolchains) {
				addTestCases(toolchain, setting, m_SVCOMP_Examples);
			}
		}
		
		for (String setting : m_Settings) {
			for (String toolchain : m_BoogieToolchains) {
				addTestCases(toolchain, setting, m_UltimateRepository, 
						new String[] {".bpl"});
			}
		}
		for (String setting : m_Settings) {
			for (String toolchain : m_CToolchains) {
				addTestCases(toolchain, setting, m_UltimateRepository, 
						new String[] {".c", ".i"});
			}
		}
		return super.createTestCases();
	}
	
	
	@Override
	protected ITestSummary[] constructTestSummaries() {
		ArrayList<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks = 
				new ArrayList<Class<? extends ICsvProviderProvider<? extends Object>>>();
		benchmarks.add(TraceAbstractionBenchmarks.class);
		benchmarks.add(Benchmark.class);

		// @formatter:off
		ColumnDefinition[] columnDef = new ColumnDefinition[] { 
						new ColumnDefinition(
								"Overall time", "Avg. runtime",
								ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),	
//						new ColumnDefinition(
//								"Peak memory consumption (bytes)", "Mem{-}ory",
//								ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average),						
						new ColumnDefinition(
								"Overall iterations", "Iter{-}ations",
								ConversionContext.Divide(1, 2, ""), Aggregate.Ignore, Aggregate.Average),
//						
						new ColumnDefinition("InterpolantConsolidationBenchmark_DifferenceAutomatonEmptyCounter", "Diff.{-}Automaton{-}Empty{-}Counter",
								ConversionContext.Divide(1, 2, ""), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("InterpolantConsolidationBenchmark_DisjunctionsGreaterOneCounter", "Disjunction{-}Greater{-}OneCounter",
						ConversionContext.Divide(1, 2, ""), Aggregate.Ignore, Aggregate.Average),
						
						new ColumnDefinition("InterpolantConsolidationBenchmark_InterpolantsDropped", "Interpolants dropped", ConversionContext.Divide(1, 2, ""), Aggregate.Ignore, Aggregate.Average),								
						new ColumnDefinition("InterpolantConsolidationBenchmark_NewlyCreatedInterpolants", "Newly Created Interpolants", ConversionContext.Divide(1, 2, ""), Aggregate.Ignore, Aggregate.Average),								
						new ColumnDefinition("EdgeCheckerBenchmarkData_Sat", "Num Sats", ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),										
						new ColumnDefinition("EdgeCheckerBenchmarkData_Unsat", "Num Unsats", ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),										
//						new ColumnDefinition("EdgeCheckerBenchmarkData_Unknown", "Num Unknown", ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Sum),										
						new ColumnDefinition("EdgeCheckerBenchmarkData_NotChecked", "Num NotChecked", ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Sum),										
						new ColumnDefinition("InterpolantConsolidationBenchmark_NumOfHoareTripleChecks", "NumOfHTC{-}Checks{-}IC", 
								ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Max),								
						new ColumnDefinition("InterpolantConsolidationBenchmark_TimeOfConsolidation", "Time{-}Of{-}Consol.", 
								ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average)
						
//						new ColumnDefinition(
//								"NumberOfCodeBlocks", null,
//								ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
//						new ColumnDefinition(
//								"NumberOfCodeBlocksAsserted", null,
//								ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),		
//						new ColumnDefinition(
//								"SizeOfPredicatesFP", null,
//								ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),	
//						new ColumnDefinition(
//								"SizeOfPredicatesBP", null,
//								ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),	
//						new ColumnDefinition(
//								"Conjuncts in SSA", null,
//								ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),	
//						new ColumnDefinition(
//								"Conjuncts in UnsatCore", null,
//								ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
//						new ColumnDefinition(
//								"ICC %", "ICC",
//								ConversionContext.Percent(true,2), Aggregate.Ignore, Aggregate.Average)						
		};
		// @formatter:on

		return new ITestSummary[] { 
				new TraceAbstractionTestSummary(this.getClass()),
				new CsvConcatenator(this.getClass(), TraceAbstractionBenchmarks.class), 
				new LatexOverviewSummary(getClass(), benchmarks, columnDef),
				//	new LatexDetailedSummary(getClass(), benchmarks, columnDef),
				//	new CsvSummary(getClass(), benchmarks, columnDef),
				//	new HTMLSummary(getClass(), benchmarks, columnDef),
				new KingOfTheHillSummary(this.getClass()),
				new StandingsSummary(this.getClass()),
		};
	}

	
}