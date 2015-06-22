package de.uni_freiburg.informatik.ultimatetest.suites.evals;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.NoTimeoutTestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.suites.AbstractEvalTestSuite;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimatetest.summaries.ConversionContext;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition.Aggregate;

public class AbstractInterpretationv2TestSuite extends AbstractEvalTestSuite {

	private static final String[] FILEENDINGS = new String[] { ".c" };

	private static final String[] TOOLCHAINS = new String[] { "AbstractInterpretationv2C.xml", };

	// @formatter:off
	private static final String[] SETTINGS = new String[] { 
		"EmptySettings.epf"
	};

	private static final DirectoryFileEndingsPair[] INPUT = new DirectoryFileEndingsPair[] {
			getPair("examples/Backtranslation/regression/c/standard"),
	};
	// @formatter:on

	@Override
	protected long getTimeout() {
		return 10 * 1000;
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
			};
		// @formatter:on
	}

	@Override
	public ITestResultDecider constructITestResultDecider(UltimateRunDefinition urd) {
		return new NoTimeoutTestResultDecider(urd);
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (String toolchain : TOOLCHAINS) {
			for (String setting : SETTINGS) {
				addTestCases(toolchain, "ai/" + setting, INPUT);
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
