package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.LTLCheckerTestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.evals.ColumnDefinition.Aggregate;

public class LTLChecker extends AbstractEvaluationTestSuite {

	@Override
	public ITestResultDecider constructITestResultDecider(UltimateRunDefinition urd) {
		return new LTLCheckerTestResultDecider(urd, false);
	}

	@Override
	protected void createTestCasesForReal(List<UltimateTestCase> testcases) {
		addTestCasesFixed("LTLAutomizerC.xml", "ltlAutomizer/LtlAutomizerC.epf", testcases);
//		addTestCasesFixed("LTLAutomizerC.xml", "ltlAutomizer/LtlAutomizerC-SBE.epf", testcases);
		addTestCasesFixed("LTLAutomizerC.xml", "ltlAutomizer/LtlAutomizerC-SBE+SimplifyAssumesSBE.epf", testcases);

//		addTestCasesFixed("LTLAutomizerC.xml", "ltlAutomizer/LtlAutomizerC-NondetBuchi.epf", testcases);

	}

	@Override
	protected int getFilesPerCategory() {
		return -1;
	}

	@Override
	protected String[] getDirectories() {
		// @formatter:off
		return new String[] { 
//				"examples/LTL/rers2012/P14/",
//				"examples/LTL/rers2012correctencoding/P14/",
//				"examples/LTL/rers2012/P15/",
//				"examples/LTL/rers2012/P16/",
//				"examples/LTL/rers2012/P17/",
//				"examples/LTL/rers2012/P18/",
//				"examples/LTL/rers2012/P19/",
				"examples/LTL/coolant/",
				"examples/LTL/koskinen/ltlcmodelchecker-benchmarks/",
//				"examples/LTL/bugs/",
//				"examples/LTL/bugs/Bug_AssumeFalse.c",
				
				//RERS examples with NO_RESULT
//				"examples/LTL/bugs/Bug_ProcedureAssumeFalse.c",
//				"examples/LTL/rers2012/P14/Problem14_prop_014.c",
//				"examples/LTL/rers2012correctencoding/P14/Problem14_prop_014.c",
				
				//Koskinen examples with problems
//				"examples/LTL/koskinen/ltlcmodelchecker-benchmarks/18-windows_os_frag4_prop2-new.c",

		};
		// @formatter:on
		// return super.getDirectories();
	}

	@Override
	protected int getTimeout() {
		return 20 * 60 * 1000;
	}

	@Override
	protected ColumnDefinition[] getColumnDefinitions() {
		// @formatter:off
		return new ColumnDefinition[]{
				new ColumnDefinition(
						"Runtime (ns)", "Total time",
						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),	
				new ColumnDefinition(
						"Allocated memory end (bytes)", "Alloc. Memory",
						ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average),
				new ColumnDefinition(
						"Peak memory consumption (bytes)", "Peak Memory",
						ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average),
						
				new ColumnDefinition(
						"Overall iterations", "Iterations",
						ConversionContext.BestFitNumber(), Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition(
						"Overall time", "BA analysis time",
						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition(
						"Minimization time", "BA minimization time",
						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),
				
				new ColumnDefinition(
						"Initial property automaton Locations", "Initial property automaton Locations",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(
						"Initial property automaton Edges", "Initial property automaton Edges",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(
						"Initial RCFG Locations", "Initial RCFG Locations",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(
						"Initial RCFG Edges", "Initial RCFG Edges",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(
						"Initial product Locations", "Initial product Locations",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(
						"Initial product Edges", "Initial product Edges",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(
						"Optimized Product Locations", "Optimized Product Locations",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(
						"Optimized Product Edges", "Optimized Product Edges",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),						
						
				new ColumnDefinition(
						"Trivial modules", "Trivial modules",
						ConversionContext.BestFitNumber(), Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition(
						"Deterministic modules", "Deterministic modules",
						ConversionContext.BestFitNumber(), Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition(
						"Nondeterministic modules", "Nondeterministic modules",
						ConversionContext.BestFitNumber(), Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition(
						"Remainer module", "Remainder",
						ConversionContext.Keep(), Aggregate.Ignore, Aggregate.Ignore),						
				new ColumnDefinition(
						"Avg Locs trivial modules", "Avg Locs trivial modules",
						ConversionContext.BestFitNumber(), Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition(
						"Avg Locs deterministic modules", "Avg Locs deterministic modules",
						ConversionContext.BestFitNumber(), Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition(
						"Avg Locs nondeterministic modules", "Avg Locs nondeterministic modules",
						ConversionContext.BestFitNumber(), Aggregate.Sum, Aggregate.Average),						
			};
		// @formatter:on
	}

	@Override
	protected String[] getFileEndings() {
		return new String[] { ".c" };
	}

}
