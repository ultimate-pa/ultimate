package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.chc;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.FastUPRBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerModuleDecompositionBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerTimingBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.CodeCheckBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.AutomizerChcTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.logs.incremental.IncrementalLogCsv;
import de.uni_freiburg.informatik.ultimate.test.logs.incremental.IncrementalLogWithBenchmarkResults;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.CsvConcatenator;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.KingOfTheHillSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.StandingsSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.TraceAbstractionTestSummary;
import de.uni_freiburg.informatik.ultimate.test.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.ultimatetest.suites.AbstractModelCheckerTestSuiteWithIncrementalLog;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.Benchmark;
import de.uni_freiburg.informatik.ultimate.util.statistics.GraphSizeCsvProvider;

public class AutomizerChcTest extends AbstractModelCheckerTestSuiteWithIncrementalLog {

	private static final String TEST_FILES_DIR = TestUtil.getPathFromTrunk("examples/smtlib/horn");
	// private static final String TEST_FILES_DIR = "/storage/chc-comp/with-result";

	private static final long TIMEOUT = 90 * 1000;

	private static final String TOOLCHAIN = "examples/toolchains/AutomizerCHC.xml";
	private static final String SETTINGS_FILE = "examples/settings/chc/AutomizerCHC/AutomizerCHC_Goto.epf";
//	private static final String SETTINGS_FILE = "examples/settings/chc/AutomizerCHC/AutomizerCHC_No_Goto.epf";

	@Override
	protected ITestSummary[] constructTestSummaries() {
		final List<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks = getBenchmarks();

		final List<ITestSummary> rtr = new ArrayList<>();
		rtr.add(new TraceAbstractionTestSummary(getClass()));
		rtr.add(new KingOfTheHillSummary(this.getClass()));
		rtr.add(new StandingsSummary(this.getClass()));
		benchmarks.stream().forEach(a -> rtr.add(new CsvConcatenator(getClass(), a)));

		return rtr.toArray(new ITestSummary[rtr.size()]);
	}

	private static List<Class<? extends ICsvProviderProvider<? extends Object>>> getBenchmarks() {
		final List<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks = new ArrayList<>();
		benchmarks.add(BuchiAutomizerTimingBenchmark.class);
		benchmarks.add(Benchmark.class);
		benchmarks.add(TraceAbstractionBenchmarks.class);
		benchmarks.add(CodeCheckBenchmarks.class);
		benchmarks.add(BuchiAutomizerModuleDecompositionBenchmark.class);
		benchmarks.add(GraphSizeCsvProvider.class);
		benchmarks.add(FastUPRBenchmark.class);
		return benchmarks;
	}

	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		final List<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks = getBenchmarks();
		final List<IIncrementalLog> incLogs = new ArrayList<>();
		incLogs.add(getIncrementalLogWithVMParameters());
		incLogs.add(new IncrementalLogWithBenchmarkResults(getClass()));
		benchmarks.stream().map(a -> new IncrementalLogCsv(getClass(), a)).forEach(incLogs::add);
		return incLogs.toArray(new IIncrementalLog[incLogs.size()]);
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		final List<UltimateTestCase> rtr = new ArrayList<>();
		final List<File> inputFiles = new ArrayList<>(getInputFiles());
		Collections.sort(inputFiles);

		final File toolchainFile = new File(TestUtil.getPathFromTrunk(TOOLCHAIN));
		final File settingsFile = new File(TestUtil.getPathFromTrunk(SETTINGS_FILE));
		for (final File inputFile : inputFiles) {
			final UltimateRunDefinition urd =
					new UltimateRunDefinition(inputFile, settingsFile, toolchainFile, TIMEOUT);
			final ITestResultDecider decider = constructITestResultDecider(urd);
			rtr.add(buildTestCase(urd, decider, inputFile.getName()));
		}

		return rtr;
	}

	public Collection<File> getInputFiles() {
		return TestUtil.getFiles(new File(TEST_FILES_DIR), new String[] { ".smt2" });
	}

	@Override
	protected long getTimeout() {
		return TIMEOUT;
	}

	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition urd) {
		return new AutomizerChcTestResultDecider(urd, true);
	}
}
