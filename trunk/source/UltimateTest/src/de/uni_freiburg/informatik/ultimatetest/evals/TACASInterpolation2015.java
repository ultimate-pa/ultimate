package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.ArrayList;
import java.util.Collection;

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
import de.uni_freiburg.informatik.ultimatetest.summary.ExtendedCsvConcatenator;
import de.uni_freiburg.informatik.ultimatetest.summary.IIncrementalLog;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.summary.IncrementalLogWithVMParameters;

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
public class TACASInterpolation2015 extends AbstractModelCheckerTestSuite {

	private IncrementalLogWithVMParameters mIncrementalLog;

	private static final String[] mDirectories = {
			// Contains pointers
			// "examples/svcomp/loops/",
			// "examples/svcomp/loop-lit/",
			// Contains arrays
			// "examples/svcomp/loop-acceleration/",

			// conains no pointers or arrays
			"examples/svcomp/ssh-simplified/",
//			"examples/svcomp/eca-rers2012/", 
			"examples/svcomp/loop-invgen/",
			"examples/svcomp/locks/",
			"examples/svcomp/loop-new/", 
			"examples/svcomp/ntdrivers-simplified/", 
			"examples/svcomp/recursive/",
			"examples/svcomp/systemc/", 
			};

	// Time out for each test case in milliseconds
	private final static int mTimeout = 60 * 1000;
	private final static String[] mFileEndings = new String[] { ".c" };

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (mTestCases.size() == 0) {
			addTestCases("AutomizerC.xml", "TACASInterpolation2015/ForwardPredicates.epf", mDirectories, mFileEndings,
					mTimeout);

			addTestCases("AutomizerC.xml", "TACASInterpolation2015/TreeInterpolation.epf", mDirectories, mFileEndings,
					mTimeout);

//			addTestCases("CodeCheckWithBE_C.xml", "TACASInterpolation2015/svComp-32bit-precise-BE-Kojak.epf",
//					mDirectories, mFileEndings, mTimeout);
//
//			addTestCases("CodeCheckWithBE_C.xml",
//					"TACASInterpolation2015/svComp-32bit-precise-BE-Kojak-SmtInterpol.epf", mDirectories, mFileEndings,
//					mTimeout);

//			addTestCases("CodeCheckWithBE_C.xml",
//					"TACASInterpolation2015/blabla-fp.epf", mDirectories, mFileEndings,
//					mTimeout);
			
			mIncrementalLog.setCountTotal(mTestCases.size());
		}
		// return Util.firstN(super.createTestCases(), 3);
		return super.createTestCases();
	}

	@Override
	public ITestResultDecider constructITestResultDecider(UltimateRunDefinition urd) {
		return new SafetyCheckTestResultDecider(urd, false);
	}

	@Override
	protected ITestSummary[] constructTestSummaries() {
		ArrayList<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks = new ArrayList<Class<? extends ICsvProviderProvider<? extends Object>>>();
		benchmarks.add(TimingBenchmark.class);
		benchmarks.add(Benchmark.class);
		benchmarks.add(TraceAbstractionBenchmarks.class);
		benchmarks.add(CodeCheckBenchmarks.class);

		return new ITestSummary[] { new ExtendedCsvConcatenator(getClass(), benchmarks),
				new TraceAbstractionTestSummary(getClass()) };
	}

	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		if (mIncrementalLog == null) {
			mIncrementalLog = new IncrementalLogWithVMParameters(this.getClass());
		}
		return new IIncrementalLog[] { mIncrementalLog };
	}

}
