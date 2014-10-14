package de.uni_freiburg.informatik.ultimatetest;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

public abstract class AbstractModelCheckerTestSuite extends UltimateTestSuite {
	protected List<UltimateTestCase> mTestCases = new ArrayList<UltimateTestCase>();
	private static final String mPathToSettings = "examples/settings/";
	private static final String mPathToToolchains = "examples/toolchains/";
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		return mTestCases;
	}
	
	public abstract ITestResultDecider constructITestResultDecider(UltimateRunDefinition ultimateRunDefinition);

	protected void addTestCases(File toolchainFile, File settingsFile, Collection<File> inputFiles, long deadline) {
		for (File inputFile : inputFiles) {
			UltimateRunDefinition urd = new UltimateRunDefinition(inputFile, settingsFile, toolchainFile);
			UltimateStarter starter = new UltimateStarter(urd, deadline);
			mTestCases.add(new UltimateTestCase(urd.generateShortStringRepresentation(),
					constructITestResultDecider(urd), 
					starter, 
					urd, 
					super.getSummaries(),
					super.getIncrementalLogs())
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

		File toolchainFile = new File(Util.getPathFromTrunk(mPathToToolchains + toolchain));
		File settingsFile = new File(Util.getPathFromTrunk(mPathToSettings + settings));
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
