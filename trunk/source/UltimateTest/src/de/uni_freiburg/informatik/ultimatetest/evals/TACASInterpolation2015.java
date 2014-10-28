package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.util.Util.IPredicate;
import de.uni_freiburg.informatik.ultimate.core.util.Util.IReduce;
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
import de.uni_freiburg.informatik.ultimatetest.evals.TACAS2015Summary.Aggregate;
import de.uni_freiburg.informatik.ultimatetest.summary.IIncrementalLog;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.summary.IncrementalLogWithVMParameters;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

/**
 * 
 * Test suite that contains the evaluation for the coming paper
 * "An interpolant generator for when you don't have an interpolant generator"
 * (see https://sotec.informatik.uni-freiburg.de/svn/swt/devel/heizmann/publish/
 * 2015TACAS-Interpolation/)
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public abstract class TACASInterpolation2015 extends AbstractModelCheckerTestSuite {

	private IncrementalLogWithVMParameters mIncrementalLog;

	// Time out for each test case in milliseconds
	private final static int mTimeout = 300 * 1000;
	private final static String[] mFileEndings = new String[] { ".c" };

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (mTestCases.size() == 0) {
			List<UltimateTestCase> testcases = new ArrayList<>();

			createTestCasesForReal(testcases);

			if (getFilesPerCategory() != -1) {
				mTestCases = testcases;
			}

			mIncrementalLog.setCountTotal(mTestCases.size());
		}
		return super.createTestCases();
	}

	protected abstract void createTestCasesForReal(List<UltimateTestCase> testcases);

	protected String[] getDirectories() {
		// @formatter:off
		String[] directories = {
				// not good for CodeCheck
//			"examples/svcomp/eca-rers2012/",
//				"examples/svcomp/loop-invgen/",
//				"examples/svcomp/loop-new/",				
				
			"examples/svcomp/ntdrivers-simplified/",
//   		"examples/svcomp/ssh-simplified/", 
//			"examples/svcomp/locks/",
//			"examples/svcomp/recursive/", 
//			"examples/svcomp/systemc/",
		};
		return directories;
		// @formatter:on
	}

	/**
	 * if -1 use all
	 * 
	 * @return
	 */
	protected abstract int getFilesPerCategory();

	protected void addTestCasesFixed(String toolchain, String setting, List<UltimateTestCase> testcases) {
		addTestCases(toolchain, setting, getDirectories(), mFileEndings, mTimeout);
		testcases.addAll(limitTestFiles());
	}

	@Override
	protected ITestSummary[] constructTestSummaries() {
		// @formatter:off
		ArrayList<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks 
			= new ArrayList<Class<? extends ICsvProviderProvider<? extends Object>>>();
		benchmarks.add(TimingBenchmark.class);
		benchmarks.add(Benchmark.class);
		benchmarks.add(TraceAbstractionBenchmarks.class);
		benchmarks.add(CodeCheckBenchmarks.class);

		ColumnDefinition[] columnDef = new ColumnDefinition[]{
			new ColumnDefinition(
					"Runtime (ns)", "Avg. runtime",
					ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),	
			new ColumnDefinition(
					"Allocated memory end (bytes)", "Mem{-}ory",
					ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average),
			new ColumnDefinition(
					"Overall iterations", "Iter{-}ations",
					ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
			new ColumnDefinition(
					"NumberOfCodeBlocks", null,
					ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
			new ColumnDefinition(
					"SizeOfPredicatesFP", null,
					ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),	
			new ColumnDefinition(
					"SizeOfPredicatesBP", null,
					ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),	
			new ColumnDefinition(
					"Conjuncts in SSA", null,
					ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),	
			new ColumnDefinition(
					"Conjuncts in UnsatCore", null,
					ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
			new ColumnDefinition(
					"ICC %", "ICC",
					ConversionContext.Percent(true,2), Aggregate.Ignore, Aggregate.Average),					
		};

		return new ITestSummary[] {
				new TACAS2015Summary(getClass(), benchmarks, columnDef),
				new TraceAbstractionTestSummary(getClass()) };

		// @formatter:on
	}

	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		if (mIncrementalLog == null) {
			mIncrementalLog = new IncrementalLogWithVMParameters(this.getClass(), mTimeout);
		}
		return new IIncrementalLog[] { mIncrementalLog };
	}

	private List<UltimateTestCase> limitTestFiles() {
		if (getFilesPerCategory() == -1) {
			return new ArrayList<>();
		}
		List<UltimateTestCase> testcases = new ArrayList<>();

		Set<String> categories = de.uni_freiburg.informatik.ultimate.core.util.Util.selectDistinct(mTestCases, new de.uni_freiburg.informatik.ultimate.core.util.Util.IReduce<String, UltimateTestCase>() {
			@Override
			public String reduce(UltimateTestCase entry) {
				return entry.getUltimateRunDefinition().getInput().getParentFile().getName();
			}
		});

		for (final String category : categories) {
			testcases.addAll(de.uni_freiburg.informatik.ultimate.core.util.Util.where(mTestCases, new de.uni_freiburg.informatik.ultimate.core.util.Util.IPredicate<UltimateTestCase>() {
				int i = 0;

				@Override
				public boolean check(UltimateTestCase entry) {
					if (entry.getUltimateRunDefinition().getInput().getParentFile().getName().equals(category)) {
						if (i < getFilesPerCategory()) {
							i++;
							return true;
						}
					}
					return false;
				}
			}));
		}
		mTestCases = new ArrayList<>();
		return testcases;
	}

	@Override
	public ITestResultDecider constructITestResultDecider(UltimateRunDefinition urd) {
		return new SafetyCheckTestResultDecider(urd, false);
	}

}
