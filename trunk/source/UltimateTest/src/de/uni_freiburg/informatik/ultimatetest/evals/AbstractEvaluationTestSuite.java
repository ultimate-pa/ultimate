package de.uni_freiburg.informatik.ultimatetest.evals;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.benchmark.SizeBenchmark;
import de.uni_freiburg.informatik.ultimate.core.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.ModuleDecompositionBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.TimingBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.CodeCheckBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.util.Benchmark;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimatetest.AbstractModelCheckerTestSuite;
import de.uni_freiburg.informatik.ultimatetest.TraceAbstractionTestSummary;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.summary.IIncrementalLog;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.summary.IncrementalLogWithVMParameters;
import de.uni_freiburg.informatik.ultimatetest.traceabstraction.TestSummaryWithBenchmarkResults;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

/**
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public abstract class AbstractEvaluationTestSuite extends AbstractModelCheckerTestSuite {

	private IncrementalLogWithVMParameters mIncrementalLog;

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (mTestCases.size() == 0) {
			List<UltimateTestCase> testcases = new ArrayList<>();

			// after this call, mTestCases is empty and testcases contains the
			// actual test cases
			createTestCasesForReal(testcases);

			mTestCases = testcases;
			mIncrementalLog.setCountTotal(mTestCases.size());
		}
		return super.createTestCases();
	}

	/**
	 * Add your testcases to the provided list with
	 * {@link #addTestCasesFixed(String, String, List)}
	 * 
	 * @param testcases
	 */
	protected abstract void createTestCasesForReal(List<UltimateTestCase> testcases);

	/**
	 * @return Timeout for each test case in milliseconds
	 */
	protected abstract int getTimeout();

	/**
	 * Which directories relative to the Ultimate trunk should be used to run
	 * the test? Per default, each subdirectory containing valid input files
	 * represents a category. You can overwrite
	 * {@link #useParentDirectoryAsCategory()} to use each entry of
	 * getDirectories as category instead.
	 */
	protected abstract String[] getDirectories();

	/**
	 * @return true iff the distinct set of parent directory names of all actual
	 *         input files should be used as category, false iff each entry of
	 *         {@link #getDirectories()} should be used as category.
	 */
	protected boolean useParentDirectoryAsCategory() {
		return true;
	}

	/**
	 * Specify how many files per directory should be used
	 * 
	 * @return if -1 use all
	 */
	protected abstract int getFilesPerCategory();

	/**
	 * Describe which columns should be present in the generated LaTeX table,
	 * based on the available {@link ICsvProviderProvider} instances during the
	 * test. Look in {@link TACAS2015} for an example.
	 */
	protected abstract ColumnDefinition[] getColumnDefinitions();

	/**
	 * Specify which files should be used, .c or .bpl (or both, if your
	 * toolchain supports it)
	 */
	protected abstract String[] getFileEndings();

	protected void addTestCasesFixed(String toolchain, String setting, List<UltimateTestCase> testcases) {
		// this method collects all wanted testcases and uses mTestCases as
		// cache
		addTestCases(toolchain, setting, getDirectories(), getFileEndings(), getTimeout());
		// this method clears mTestcases and adds the real selection to the
		// testcases list
		limitTestFiles(testcases);
	}

	@Override
	protected ITestSummary[] constructTestSummaries() {
		ArrayList<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks = new ArrayList<Class<? extends ICsvProviderProvider<? extends Object>>>();
		benchmarks.add(TimingBenchmark.class);
		benchmarks.add(Benchmark.class);
		benchmarks.add(TraceAbstractionBenchmarks.class);
		benchmarks.add(CodeCheckBenchmarks.class);
		benchmarks.add(ModuleDecompositionBenchmark.class);
		benchmarks.add(SizeBenchmark.class);

		ColumnDefinition[] columnDef = getColumnDefinitions();

		return new ITestSummary[] { 
				new LatexOverviewSummary(getClass(), benchmarks, columnDef),
				new TraceAbstractionTestSummary(getClass()), 
				new CsvSummary(getClass(), benchmarks, columnDef),
				new HTMLSummary(getClass(), benchmarks, columnDef)
		};

	}

	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		if (mIncrementalLog == null) {
			mIncrementalLog = new IncrementalLogWithVMParameters(this.getClass(), getTimeout());
		}
		return new IIncrementalLog[] { mIncrementalLog, new TestSummaryWithBenchmarkResults(this.getClass()) };
	}

	private void limitTestFiles(List<UltimateTestCase> testcases) {
		if (getFilesPerCategory() == -1) {
			// just take them all
			testcases.addAll(mTestCases);
			mTestCases = new ArrayList<>();
			return;
		}

		List<UltimateTestCase> currentTestcases = new ArrayList<>();
		Set<String> categories = null;
		if (useParentDirectoryAsCategory()) {
			categories = CoreUtil.selectDistinct(mTestCases, new CoreUtil.IReduce<String, UltimateTestCase>() {
				@Override
				public String reduce(UltimateTestCase entry) {
					return entry.getUltimateRunDefinition().getInput().getParentFile().getAbsolutePath();
				}
			});
		} else {
			categories = new HashSet<>();
			for (String dir : getDirectories()) {
				categories.add(new File(Util.getPathFromTrunk(dir)).getAbsolutePath());
			}
		}

		for (final String category : categories) {
			currentTestcases.addAll(CoreUtil.where(mTestCases, new CoreUtil.IPredicate<UltimateTestCase>() {
				int i = 0;

				@Override
				public boolean check(UltimateTestCase entry) {
					if (entry.getUltimateRunDefinition().getInput().getAbsolutePath().startsWith(category)) {
						if (i < getFilesPerCategory()) {
							i++;
							return true;
						}
					}
					return false;
				}
			}));
		}
		testcases.addAll(currentTestcases);
		mTestCases = new ArrayList<>();
	}

	@Override
	public ITestResultDecider constructITestResultDecider(UltimateRunDefinition urd) {
		return new SafetyCheckTestResultDecider(urd, false);
	}

}
