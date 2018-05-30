package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.treeautomizer;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.decider.TreeAutomizerTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.logs.incremental.IncrementalLogWithBenchmarkResults;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.CsvConcatenator;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.TraceAbstractionTestSummary;
import de.uni_freiburg.informatik.ultimate.test.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;

public class TreeAutomizerTest extends UltimateTestSuite {

//	private static final String TEST_FILES_DIR = TestUtil.getPathFromTrunk("examples/smtlib/horn");
	private static final String TEST_FILES_DIR = "/storage/chc-comp/with-result";

	private static final long TIMEOUT = 90*1000;

	private static final String TOOLCHAIN = "examples/toolchains/AutomizerCHC.xml";
	private static final String SETTINGS_FILE = "examples/settings/chccomp2018/chcToBoogie_automizer.epf";

	@Override
	protected ITestSummary[] constructTestSummaries() {
		return new ITestSummary[] { new TraceAbstractionTestSummary(this.getClass()),
				new CsvConcatenator(this.getClass(), TraceAbstractionBenchmarks.class) };
	}
	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		return new IIncrementalLog[] { new IncrementalLogWithBenchmarkResults(this.getClass()) };
	}

	@Override
	protected Collection<UltimateTestCase> createTestCases() {
		final List<UltimateTestCase> rtr = new ArrayList<>();
		final List<File> inputFiles = new ArrayList<>(getInputFiles());
		Collections.sort(inputFiles);

		final File toolchainFile = new File(TestUtil.getPathFromTrunk(TOOLCHAIN));
		final File settingsFile = new File(TestUtil.getPathFromTrunk(SETTINGS_FILE));
		for (final File inputFile : inputFiles) {
			final UltimateRunDefinition urd =
					new UltimateRunDefinition(inputFile, settingsFile, toolchainFile, TIMEOUT);
			final TreeAutomizerTestResultDecider decider = new TreeAutomizerTestResultDecider(urd, true);

			rtr.add(buildTestCase(urd, decider, inputFile.getName()));
		}

		return rtr;
	}


	public Collection<File> getInputFiles() {
		return TestUtil.getFiles(new File(TEST_FILES_DIR), new String[] { ".smt2" });
	}
}
