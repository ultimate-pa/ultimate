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
		return -1;
	}

	@Override
	protected String[] getDirectories() {
		// @formatter:off
		return new String[] { 
//				"examples/LTL/rers/",
//				"examples/LTL/coolant/",
				"examples/LTL/bugs/",
//				"examples/LTL/system/battery_control.c"

				//all the examples that had soundness errors  
//				"examples/LTL/rers/Problem14_prop_003.c",
//				"examples/LTL/rers/Problem14_prop_018.c",
//				"examples/LTL/rers/Problem15_prop_005.c",
//				"examples/LTL/rers/Problem16_prop_000.c",
//				"examples/LTL/rers/Problem16_prop_001.c",
//				"examples/LTL/rers/Problem16_prop_020.c",
//				"examples/LTL/rers/Problem16_prop_033.c",
//				"examples/LTL/rers/Problem17_prop_005.c",
//				"examples/LTL/rers/Problem17_prop_048.c",
//				// all examples that succeeded
//				"examples/LTL/rers/Problem14_prop_015.c",
//				"examples/LTL/rers/Problem14_prop_024.c",
//				"examples/LTL/rers/Problem14_prop_025.c",
//				"examples/LTL/rers/Problem15_prop_012.c",
//				"examples/LTL/rers/Problem15_prop_021.c",
//				"examples/LTL/rers/Problem16_prop_017.c",
//				"examples/LTL/rers/Problem17_prop_021.c",
//				"examples/LTL/rers/Problem17_prop_025.c",
//				"examples/LTL/rers/Problem18_prop_045.c",
//				"examples/LTL/rers/Problem18_prop_049.c",

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
