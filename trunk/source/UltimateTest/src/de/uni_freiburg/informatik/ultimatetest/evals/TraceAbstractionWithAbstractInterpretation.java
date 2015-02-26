package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.evals.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;

public class TraceAbstractionWithAbstractInterpretation extends AbstractEvaluationTestSuite {

	@Override
	protected void createTestCasesForReal(List<UltimateTestCase> testcases) {
//		addTestCasesFixed("AbstractInterpretationC.xml", "AbsIntOrTASingle.epf", testcases);
//		addTestCasesFixed("AutomizerC.xml", "ai/Automizer.epf", testcases);
		addTestCasesFixed("AutomizerC.xml", "ai/Automizer+AI.epf", testcases);
//		addTestCasesFixed("AutomizerC.xml", "ai/Automizer+AI-Fast.epf", testcases);
	}

	@Override
	protected int getFilesPerCategory() {
		return -1;
	}

	@Override
	protected boolean useParentDirectoryAsCategory() {
		return false;
	}

	@Override
	protected String[] getDirectories() {
		// @formatter:off
		return new String[] { 
//				"examples/programs/regression/c/", 
//				"examples/svcomp/locks/",

				// current bugs:
				"examples/programs/regression/c/NestedDeclarators.c",
		};
		// @formatter:on
	}

	@Override
	protected int getTimeout() {
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

	@Override
	protected String[] getFileEndings() {
		return new String[] { ".c" };
	}

	@Override
	protected ITestSummary[] constructTestSummaries() {
		ITestSummary[] summaries = super.constructTestSummaries();
		ArrayList<ITestSummary> rtr = new ArrayList<>();
		for (ITestSummary summary : summaries) {
			rtr.add(summary);
		}
		rtr.add(new ComparativeSummary(getClass()));
		return rtr.toArray(new ITestSummary[0]);
	}

}
