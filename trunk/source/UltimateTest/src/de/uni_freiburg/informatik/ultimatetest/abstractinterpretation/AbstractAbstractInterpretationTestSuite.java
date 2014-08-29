/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.abstractinterpretation;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateStarter;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

/**
 * Stolen from AbstractTraceAbstractionTestSuite ;-)
 */
public class AbstractAbstractInterpretationTestSuite extends UltimateTestSuite {
	private List<UltimateTestCase> m_testCases;

	private static final String m_PathToSettings = "examples/settings/";
	private static final String m_PathToToolchains = "examples/toolchains/";
	
	@Override
	protected ITestSummary[] constructTestSummaries() {
		return new ITestSummary[] {
				new AbstractInterpretationTestSummary(this.getClass()),
				new AbstractInterpretationLaTeXTestSummary(this.getClass()),
				new AbstractInterpretationComparisonTestSummary(this.getClass())
		};
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		return m_testCases;
	}

	protected void addTestCases(File toolchainFile, File settingsFile, Collection<File> inputFiles, String description,
			String uniqueString, long deadline) {
		if (m_testCases == null) {
			m_testCases = new ArrayList<UltimateTestCase>();
		}
		
		for (File inputFile : inputFiles) {
			UltimateRunDefinition urd = new UltimateRunDefinition(inputFile, settingsFile, toolchainFile);
			UltimateStarter starter = new UltimateStarter(urd, deadline, null, null);
			m_testCases.add(new UltimateTestCase(starter,
						new AbstractInterpretationTestResultDecider(inputFile, uniqueString),
						super.getSummaries(),
					uniqueString + "_" + inputFile.getAbsolutePath(), urd));
		}
	}

	/**
	 * @param toolchain
	 * @param settings
	 * @param directory
	 * @param fileEndings
	 * @param description
	 * @param uniqueString
	 * @param deadline
	 */
	protected void addTestCases(String toolchain, String settings, String[] directories, String[] fileEndings,
			String description, String uniqueString, long deadline) {

		File toolchainFile = new File(Util.getPathFromTrunk(m_PathToToolchains + toolchain));
		File settingsFile = new File(Util.getPathFromTrunk(m_PathToSettings + settings));
		Collection<File> testFiles = new ArrayList<File>();
		for (String directory : directories) {
			testFiles.addAll(getInputFiles(directory, fileEndings));
		}
		addTestCases(toolchainFile, settingsFile, testFiles, description, uniqueString, deadline);
	}

	private Collection<File> getInputFiles(String directory, String[] fileEndings) {
		return Util.getFiles(new File(Util.getPathFromTrunk(directory)), fileEndings);
	}
}
