package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.LTLCheckerTestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.evals.LatexSummary.Aggregate;

public class LTLChecker extends AbstractEvaluationTestSuite {

	@Override
	public ITestResultDecider constructITestResultDecider(UltimateRunDefinition urd) {
		return new LTLCheckerTestResultDecider(urd, false);
	}

	@Override
	protected void createTestCasesForReal(List<UltimateTestCase> testcases) {
		addTestCasesFixed("LtlSoftwareModelCheckingC.xml", "LtlSoftwareModelCheckingC.epf", testcases);
	}

	@Override
	protected int getFilesPerCategory() {
		return 20;
	}

	@Override
	protected String[] getDirectories() {
		// @formatter:off
		return new String[] { 
				"examples/LTL/rers/", 
//				"examples/LTL/system/battery_control.c"
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

}
