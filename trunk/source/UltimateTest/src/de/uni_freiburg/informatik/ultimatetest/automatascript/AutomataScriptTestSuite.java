package de.uni_freiburg.informatik.ultimatetest.automatascript;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateStarter;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

public class AutomataScriptTestSuite extends UltimateTestSuite {
	
	
	private static final String m_Toolchain = "examples/toolchains/AutomataScriptInterpreter.xml";
	private static final File m_ToolchainFile = new File(Util.getPathFromTrunk(m_Toolchain));
	private static int m_Timeout = 60000;
	private static String m_Description = "AutomataScriptTest";
	private static final String[] m_Directories = { 
		"examples/programs" 
		};
	private static final String[] m_FileEndings = { ".ats" };
	

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		List<UltimateTestCase> testCases = new ArrayList<UltimateTestCase>();

		String summaryLogFileName = Util.generateSummaryLogFilename(
				Util.getPathFromSurefire(".", this.getClass().getCanonicalName()), m_Description);
		AutomataScriptTestSummary testResultSummary = new AutomataScriptTestSummary(this.getClass().getCanonicalName(), summaryLogFileName);
		getSummaries().add(testResultSummary);

		Collection<File> inputFiles = new ArrayList<File>();
		for (String directory : m_Directories) {
			inputFiles.addAll(getInputFiles(directory, m_FileEndings));
		}

		for (File inputFile : inputFiles) {
			File settingsFile = null;
			UltimateStarter starter = new UltimateStarter(inputFile, settingsFile , m_ToolchainFile, m_Timeout, null, null);
			UltimateTestCase utc = new UltimateTestCase(
					starter,
					new AutomataScriptTestResultDecider(), 
					testResultSummary, 
					m_Description + "_" + inputFile.getAbsolutePath(), 
					inputFile.getAbsolutePath());
			testCases.add(utc);
		}
		return testCases;
	}
	
	private Collection<File> getInputFiles(String directory, String[] fileEndings) {
		return Util.getFiles(new File(Util.getPathFromTrunk(directory)), fileEndings);
	}

}
