package de.uni_freiburg.informatik.ultimatetest;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

public abstract class AbstractModelCheckerTestSuite extends UltimateTestSuite {
	protected List<UltimateTestCase> mTestCases = new ArrayList<UltimateTestCase>();
	private static final String mPathToSettings = "examples/settings/";
	private static final String mPathToToolchains = "examples/toolchains/";
	
	/**
	 * Timeout of each test case.
	 * @return A timeout for each test case in ms. The value 0 means that there
	 * is no timeout. Negative values are forbidden.
	 * This will override the timeout that is specified in the settings files.
	 */
	protected abstract long getTimeout();

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		return mTestCases;
	}

	public abstract ITestResultDecider constructITestResultDecider(UltimateRunDefinition ultimateRunDefinition);

	protected void addTestCase(File toolchainFile, File settingsFile, File inputFile, ITestResultDecider testResultDecider) {
		long deadline = getTimeout();
		assert deadline >= 0;
		UltimateRunDefinition urd = new UltimateRunDefinition(inputFile, settingsFile, toolchainFile);
		UltimateStarter starter = new UltimateStarter(urd, deadline);
		mTestCases.add(new UltimateTestCase(urd.generateShortStringRepresentation(), testResultDecider, starter, urd,
				super.getSummaries(), super.getIncrementalLogs()));

	}

	protected void addTestCases(File toolchainFile, File settingsFile, Collection<File> inputFiles) {
		long deadline = getTimeout();
		assert deadline >= 0;
		for (File inputFile : inputFiles) {
			UltimateRunDefinition urd = new UltimateRunDefinition(inputFile, settingsFile, toolchainFile);
			UltimateStarter starter = new UltimateStarter(urd, deadline);
			mTestCases.add(new UltimateTestCase(urd.generateShortStringRepresentation(),
					constructITestResultDecider(urd), starter, urd, super.getSummaries(), super.getIncrementalLogs()));
		}
	}

	/**
	 * Add a single test case with paths relative to the ultimate trunk
	 * 
	 * @param toolchain
	 *            A string specifying a valid path to a toolchain file relative
	 *            to trunk/examples/toolchain
	 * @param settings
	 *            A string specifying a valid path to a setting file relative to
	 *            trunk/examples/settings
	 * @param input
	 *            A string specifying a valid path to an input file relative to
	 *            trunk/examples
	 * @param testResultDecider
	 *            The test result decider that should be used in this test
	 */
	protected void addTestCase(String toolchain, String settings, String input, ITestResultDecider testResultDecider) {
		File toolchainFile = new File(Util.getPathFromTrunk(mPathToToolchains + toolchain));
		File settingsFile = new File(Util.getPathFromTrunk(mPathToSettings + settings));
		File inputFile = new File(Util.getPathFromTrunk(input));
		addTestCase(toolchainFile, settingsFile, inputFile, testResultDecider);
	}

	protected void addTestCase(String toolchain, String settings, String input) {
		File toolchainFile = new File(Util.getPathFromTrunk(mPathToToolchains + toolchain));
		File settingsFile = new File(Util.getPathFromTrunk(mPathToSettings + settings));
		File inputFile = new File(Util.getPathFromTrunk(input));
		addTestCases(toolchainFile, settingsFile, Collections.singleton(inputFile));
	}

	protected void addTestCases(String toolchain, String settings, String[] directories, String[] fileEndings) {
		File toolchainFile = new File(Util.getPathFromTrunk(mPathToToolchains + toolchain));
		File settingsFile = new File(Util.getPathFromTrunk(mPathToSettings + settings));
		Collection<File> testFiles = new ArrayList<File>();
		for (String directory : directories) {
			testFiles.addAll(getInputFiles(directory, fileEndings));
		}
		addTestCases(toolchainFile, settingsFile, testFiles);
	}
	
	protected void addTestCasesRegExp(String toolchain, String settings, String[] regExp) {

		File toolchainFile = new File(Util.getPathFromTrunk(mPathToToolchains + toolchain));
		File settingsFile = new File(Util.getPathFromTrunk(mPathToSettings + settings));
		File trunk = new File(Util.getPathFromTrunk("/"));
		Collection<File> testFiles = Util.getFilesRegex(trunk, regExp);
		addTestCases(toolchainFile, settingsFile, testFiles);
	}

	protected void addTestCases(String toolchain, String settings,
			DirectoryFileEndingsPair[] directoryFileEndingsPairs) {

		File toolchainFile = new File(Util.getPathFromTrunk(mPathToToolchains + toolchain));
		File settingsFile = new File(Util.getPathFromTrunk(mPathToSettings + settings));
		Collection<File> testFiles = new ArrayList<File>();
		for (DirectoryFileEndingsPair directoryFileEndingsPair : directoryFileEndingsPairs) {
			testFiles.addAll(getInputFiles(directoryFileEndingsPair.getDirectory(),
					directoryFileEndingsPair.getFileEndings()));
		}
		addTestCases(toolchainFile, settingsFile, testFiles);
	}

	private Collection<File> getInputFiles(String directory, String[] fileEndings) {
		return Util.getFiles(new File(Util.getPathFromTrunk(directory)), fileEndings);
	}

	public static class DirectoryFileEndingsPair {
		private final String m_Directory;
		private final String[] m_FileEndings;

		public DirectoryFileEndingsPair(String directory, String[] fileEndings) {
			super();
			m_Directory = directory;
			m_FileEndings = fileEndings;
		}

		public String getDirectory() {
			return m_Directory;
		}

		public String[] getFileEndings() {
			return m_FileEndings;
		}

	}

}
