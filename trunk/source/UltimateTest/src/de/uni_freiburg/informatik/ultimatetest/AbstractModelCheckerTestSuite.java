package de.uni_freiburg.informatik.ultimatetest;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.summary.CsvConcatenator;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.traceabstraction.TestSummaryWithBenchmarkResults;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

public abstract class AbstractModelCheckerTestSuite extends UltimateTestSuite {
	private List<UltimateTestCase> m_testCases = new ArrayList<UltimateTestCase>();
	private static final String m_PathToSettings = "examples/settings/";
	private static final String m_PathToToolchains = "examples/toolchains/";
	

	@Override
	protected ITestSummary[] constructTestSummaries() {
		return new ITestSummary[] {
				new TestSummaryWithBenchmarkResults(this.getClass()),
				new TraceAbstractionTestSummary(this.getClass()),
				new CsvConcatenator(this.getClass(), TraceAbstractionBenchmarks.class)
		};
	}


	@Override
	public Collection<UltimateTestCase> createTestCases() {
		return m_testCases;
	}
	
	public abstract ITestResultDecider constructITestResultDecider(UltimateRunDefinition ultimateRunDefinition);

	protected void addTestCases(File toolchainFile, File settingsFile, Collection<File> inputFiles, long deadline) {
		for (File inputFile : inputFiles) {
			UltimateRunDefinition urd = new UltimateRunDefinition(inputFile, settingsFile, toolchainFile);
			UltimateStarter starter = new UltimateStarter(urd, deadline, null, null);
			m_testCases.add(new UltimateTestCase(starter,
					constructITestResultDecider(urd), 
					super.getSummaries(), 
					urd.generateShortStringRepresentation(), 
					urd)
			);
		}
	}

	/**
	 * 
	 * @param toolchain
	 * @param settings
	 * @param directory
	 * @param fileEndings
	 * @param description
	 * @param uniqueString
	 * @param deadline
	 */
	protected void addTestCases(String toolchain, String settings, 
			String[] directories, String[] fileEndings,	long deadline) {

		File toolchainFile = new File(Util.getPathFromTrunk(m_PathToToolchains + toolchain));
		File settingsFile = new File(Util.getPathFromTrunk(m_PathToSettings + settings));
		Collection<File> testFiles = new ArrayList<File>();
		for (String directory : directories) {
			testFiles.addAll(getInputFiles(directory, fileEndings));
		}
		addTestCases(toolchainFile, settingsFile, testFiles, deadline);
	}

	private Collection<File> getInputFiles(String directory, String[] fileEndings) {
		return Util.getFiles(new File(Util.getPathFromTrunk(directory)), fileEndings);
	}

}
