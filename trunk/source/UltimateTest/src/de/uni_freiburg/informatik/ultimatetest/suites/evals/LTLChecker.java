package de.uni_freiburg.informatik.ultimatetest.suites.evals;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.LTLCheckerTestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.suites.AbstractEvalTestSuite;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimatetest.summaries.ConversionContext;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition.Aggregate;

public class LTLChecker extends AbstractEvalTestSuite {

	private static final String[] FILEENDINGS = new String[] { ".c" };

	private static final String[] TOOLCHAINS = new String[] { 
//		"LTLAutomizerC.xml", 
		"LTLAutomizerCInline.xml", };

	// @formatter:off
	private static final String[] SETTINGS = new String[] { 
//		//no optimizations 
//		"None.epf", 
//		
//		//only small and large block encoding 
//		"None+SBE.epf",
//		"None+SBE+SASBE.epf",
//		"None+LBE-Multi.epf", 
//		
//		// only local optimizations (sink states, final states, locally infeasible edges) 
//		"Default.epf", 
//
//		//small block encoding + local optimizations 
//		"Default+SBE.epf", 
//		"Default+SBE+SASBE.epf",
//		
//		//large block encoding + local optimizations 
//		"Default-LBE-Multi.epf",
//		"Default-LBE-Multi+IB.epf",
//		"Default-LBE-Single.epf", 
//		"Default-LBE-SNME.epf",
//		
//		//different solvers
//		"Default-LBE-Multi-SMTInterpol.epf",
//		"Default-LBE-Multi-z3.epf", 
//		"Default-LBE-Multi-z3interpol.epf",
//		
//		//different buchi automata constructions 
//		"Default-LBE-Multi-StagedBlast.epf",
//		"Default-LBE-Multi+NondetBuchi.epf", 
//		"None-StagedBlast.epf",
//		 
//		//nearly all optimizations 
//		"Default-LBE-Multi+SBE.epf",
//		"Default-LBE-Multi+SBE+IB.epf", 
//		"Default-LBE-Multi+SBE+SASBE.epf", 
//		"Default-LBE-Multi+SBE+SASBE+IB.epf",
//		
//		// nearly all optimizations and staged blast 
//		"Default-LBE-Multi+SBE-StagedBlast.epf",
//		"Default-LBE-Multi+SBE+IB-StagedBlast.epf", 
		"Default-LBE-Multi+SBE+SASBE-StagedBlast.epf", 
//		"Default-LBE-Multi+SBE+SASBE+IB-StagedBlast.epf",
	};

	private static final DirectoryFileEndingsPair[] INPUT = new DirectoryFileEndingsPair[] {
//			getPair("examples/LTL/rers2012/P14/", 1), 
//			getPair("examples/LTL/rers2012/P15/", 1),
//			getPair("examples/LTL/rers2012/P16/", 1), 
//			getPair("examples/LTL/rers2012/P17/", 1),
//			getPair("examples/LTL/rers2012/P18/", 1), 
//			getPair("examples/LTL/rers2012/P19/", 1),

//			getPair("examples/LTL/rers2012correctencoding/P15/"),
//			getPair("examples/LTL/rers2012correctencoding/P16/"),
//			getPair("examples/LTL/rers2012correctencoding/P17/"),
//			getPair("examples/LTL/rers2012correctencoding/P18/"),
//			getPair("examples/LTL/rers2012correctencoding/P19/"),
//			getPair("examples/LTL/rers2012correctencoding/P14/"),
//
//			getPair("examples/LTL/coolant/"), 
//			getPair("examples/LTL/koskinen/ltlcmodelchecker-benchmarks/"),
//			getPair("examples/LTL/bugs/"), 
//			getPair("examples/LTL/simple/"),
		getPair("examples/LTL/rers2012correctencoding/P14/Problem14_prop_017.c")

	// Possible soundness bug
//	 getPair("examples/LTL/rers2012/P14/Problem14_prop_003.c"),

	};
	// @formatter:on

	@Override
	protected long getTimeout() {
		// return 180 * 1000;
		return 12 * 60 * 1000;
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
	public ITestResultDecider constructITestResultDecider(UltimateRunDefinition urd) {
		return new LTLCheckerTestResultDecider(urd, false);
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (String toolchain : TOOLCHAINS) {
			for (String setting : SETTINGS) {
				addTestCases(toolchain, "ltlAutomizer/" + setting, INPUT);
			}
		}
		return super.createTestCases();
	}

	private static DirectoryFileEndingsPair getPair(String directory, int limit) {
		return new DirectoryFileEndingsPair(directory, FILEENDINGS, limit);
	}

	private static DirectoryFileEndingsPair getPair(String directory) {
		return new DirectoryFileEndingsPair(directory, FILEENDINGS);
	}
}
