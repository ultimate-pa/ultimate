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
				"examples/LTL/koskinen/ltlcmodelchecker-benchmarks/",
//				"examples/LTL/system/timer-intermediate.c"

//				"examples/LTL/koskinen/ltlcmodelchecker-benchmarks/11-apache_accept_liveness.c",
				
				//java.lang.UnsupportedOperationException: function symbols not yet supported

				//"variables on heap are not supported in ACSL code right now."
//				"examples/LTL/koskinen/ltlcmodelchecker-benchmarks/win5_original_safe_sftylifeness.c",
				
				//RERS examples with soundness errors  
//				"examples/LTL/rers/Problem14_prop_010.c",
//				"examples/LTL/rers/Problem14_prop_002.c",

		};
		// @formatter:on
		// return super.getDirectories();
	}

	@Override
	protected int getTimeout() {
		return 2 * 60 * 1000;
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
