package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateStarter;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.Util;

public abstract class AbstractTraceAbstractionTestSuite extends UltimateTestSuite {
	private List<UltimateTestCase> m_testCases;
	private String m_summaryLogFileName;
	
	protected static final String m_ToolchainTraceAbstraction = "TraceAbstraction.xml";
	protected static final String m_ToolchainTraceAbstractionC = "TraceAbstractionC.xml";
	protected static final String m_SettingsFileBackwardPredicates = "settingsBackwardPredicates";
	protected static final String m_SettingsFileForwardPredicates = "settingsForwardPredicates";
	protected static final String m_PathToSettings = "examples/settings/traceAbstractionTestSuite/";
	protected static final String m_PathToToolchains = "examples/toolchains/";
	
	/*
	 * Following fields should be initialized in the corresponding constructor as may be required.
	 */
	protected static boolean m_TestBoogieFiles;
	protected static boolean m_TestCFiles;
	protected static boolean m_useForwardPredicates;
	protected static boolean m_useBackwardPredicates;
	// Time out for each test case in seconds
	protected static int m_Timeout;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (m_TestBoogieFiles) {
			File toolchainFile = new File(
					Util.getPathFromTrunk(m_PathToToolchains + m_ToolchainTraceAbstraction));
			File settingsFile = null;
			String description = "TraceAbstraction via "; 
			if (m_useForwardPredicates && !m_useBackwardPredicates ) {
				settingsFile = new File(Util.getPathFromTrunk(
						m_PathToSettings + m_SettingsFileForwardPredicates));
				description += "Forward Predicates (SP)";
			} else if (!m_useForwardPredicates && m_useBackwardPredicates) {
				settingsFile = new File(Util.getPathFromTrunk(
						m_PathToSettings + m_SettingsFileBackwardPredicates));
				description += "Backward Predicates (WP)";
			}
				
			addTestCases(toolchainFile, settingsFile, 
					getInputFiles(new String[] {".bpl"}),
					description, m_Timeout);
		}
		
		if (m_TestCFiles) {
			File toolchainFile = new File(
					Util.getPathFromTrunk(m_PathToToolchains + m_ToolchainTraceAbstractionC));
			File settingsFile = null;
			String description = "TraceAbstraction via "; 
			if (m_useForwardPredicates && !m_useBackwardPredicates ) {
				settingsFile = new File(Util.getPathFromTrunk(
						m_PathToSettings + m_SettingsFileForwardPredicates));
				description += "Forward Predicates (SP)";
			} else if (!m_useForwardPredicates && m_useBackwardPredicates) {
				settingsFile = new File(Util.getPathFromTrunk(
						m_PathToSettings + m_SettingsFileBackwardPredicates));
				description += "Backward Predicates (WP)";
			}
			addTestCases(toolchainFile, settingsFile, 
					getInputFiles(new String[] {".c"}),
					description, m_Timeout);
		}
		return m_testCases;

	}
	
	protected void addTestCases(File toolchainFile, File settingsFile,
			Collection<File> inputFiles,
			String description,
			long deadline) {
		if (m_testCases == null) {
			m_testCases = new ArrayList<UltimateTestCase>();
		}
		if (m_summaryLogFileName == null) {
			m_summaryLogFileName = Util.generateSummaryLogFilename(
					Util.getPathFromSurefire(".", this.getClass().getCanonicalName()), description);
		}
		TraceAbstractionTestSummary summary = new TraceAbstractionTestSummary(this.getClass().getCanonicalName(),
				m_summaryLogFileName,
				description);
		getSummaries().add(summary);
		
		for (File inputFile : inputFiles) {
			UltimateStarter starter = new UltimateStarter(inputFile, settingsFile,
					toolchainFile, deadline, null, null);
			m_testCases.add(new UltimateTestCase(starter,
					new TraceAbstractionTestResultDecider(inputFile, summary), 
					inputFile.getAbsolutePath()));
		}
	}
	
	protected abstract Collection<File> getInputFiles(String[] fileEndings);

}
