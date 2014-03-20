package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.TraceAbstractionTestSummary;
import de.uni_freiburg.informatik.ultimatetest.UltimateStarter;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

public abstract class AbstractTraceAbstractionTestSuite extends UltimateTestSuite {
	private List<UltimateTestCase> m_testCases;
	private String m_summaryLogFileName;
	private TraceAbstractionTestSummary m_Summary;
	
	private static final String m_PathToSettings = "examples/settings/traceAbstractionTestSuite/";
	private static final String m_PathToToolchains = "examples/toolchains/";

	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		return m_testCases;
	}
	
	protected void addTestCases(File toolchainFile, File settingsFile,
			Collection<File> inputFiles,
			String description,
			String uniqueString,
			long deadline) {
		if (m_testCases == null) {
			m_testCases = new ArrayList<UltimateTestCase>();
		}
		if (m_summaryLogFileName == null) {
			m_summaryLogFileName = Util.generateSummaryLogFilename(
					Util.getPathFromSurefire(".", this.getClass().getCanonicalName()), description);
		}
		if (m_Summary == null) {
			m_Summary = new TraceAbstractionTestSummary(this.getClass().getCanonicalName(),
					m_summaryLogFileName);
		}
		getSummaries().add(m_Summary);
		for (File inputFile : inputFiles) {
			UltimateStarter starter = new UltimateStarter(inputFile, settingsFile,
					toolchainFile, deadline, null, null);
			m_testCases.add(new UltimateTestCase(starter,
					new TraceAbstractionTestResultDecider(inputFile), 
					m_Summary, uniqueString + "_" + inputFile.getAbsolutePath(), inputFile.getAbsolutePath()));
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
			String directory,
			String[] fileEndings,
			String description,
			String uniqueString,
			long deadline) {
		
		File toolchainFile = new File(
				Util.getPathFromTrunk(m_PathToToolchains + toolchain));
		File settingsFile = new File(Util.getPathFromTrunk(
				m_PathToSettings + settings));
		Collection<File> testFiles = getInputFiles(directory, fileEndings);
		addTestCases(toolchainFile, settingsFile, testFiles, description, uniqueString, deadline);
	}
	
	private Collection<File> getInputFiles(String directory, String[] fileEndings) {
		return Util.getFiles(new File(Util.getPathFromTrunk(directory)),
				fileEndings);
	}

}
