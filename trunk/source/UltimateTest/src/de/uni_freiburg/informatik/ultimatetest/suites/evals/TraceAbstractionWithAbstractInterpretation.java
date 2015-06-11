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
