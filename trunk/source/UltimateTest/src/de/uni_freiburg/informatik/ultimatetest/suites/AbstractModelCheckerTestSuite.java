/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Test Library.
 * 
 * The ULTIMATE Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Test Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Test Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimatetest.suites;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateStarter;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.util.TestUtil;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class AbstractModelCheckerTestSuite extends UltimateTestSuite {
	private static final String SETTINGS_PATH = "examples/settings/";
	private static final String TOOLCHAIN_PATH = "examples/toolchains/";

	protected List<UltimateTestCase> mTestCases = new ArrayList<UltimateTestCase>();

	/**
	 * Timeout of each test case.
	 * 
	 * @return A timeout for each test case in ms. The value 0 means that there is no timeout. Negative values are
	 *         forbidden. This will override the timeout that is specified in the settings files.
	 */
	protected abstract long getTimeout();

	protected abstract ITestResultDecider constructITestResultDecider(UltimateRunDefinition ultimateRunDefinition);

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		mTestCases.sort(null);
		return mTestCases;
	}

	protected void addTestCase(File toolchainFile, File settingsFile, File inputFile,
			ITestResultDecider testResultDecider) {
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
	 *            A string specifying a valid path to a toolchain file relative to trunk/examples/toolchain
	 * @param settings
	 *            A string specifying a valid path to a setting file relative to trunk/examples/settings
	 * @param input
	 *            A string specifying a valid path to an input file relative to trunk/examples
	 * @param testResultDecider
	 *            The test result decider that should be used in this test
	 */
	protected void addTestCase(String toolchain, String settings, String input, ITestResultDecider testResultDecider) {
		File toolchainFile = getToolchainFile(toolchain);
		File settingsFile = getSettingsFile(settings);
		File inputFile = getInputFile(input);
		addTestCase(toolchainFile, settingsFile, inputFile, testResultDecider);
	}

	protected void addTestCase(String toolchain, String settings, String input) {
		File toolchainFile = getToolchainFile(toolchain);
		File settingsFile = getSettingsFile(settings);
		File inputFile = getInputFile(input);
		addTestCases(toolchainFile, settingsFile, Collections.singleton(inputFile));
	}

	protected File getInputFile(String input) {
		return new File(TestUtil.getPathFromTrunk(input));
	}

	protected File getSettingsFile(String settings) {
		return new File(TestUtil.getPathFromTrunk(SETTINGS_PATH + settings));
	}

	protected File getToolchainFile(String toolchain) {
		return new File(TestUtil.getPathFromTrunk(TOOLCHAIN_PATH + toolchain));
	}

	protected void addTestCases(String toolchain, String settings, String[] directories, String[] fileEndings) {
		File toolchainFile = getToolchainFile(toolchain);
		File settingsFile = getSettingsFile(settings);
		Collection<File> testFiles = new ArrayList<File>();
		for (String directory : directories) {
			testFiles.addAll(getInputFiles(directory, fileEndings, Integer.MAX_VALUE));
		}
		addTestCases(toolchainFile, settingsFile, testFiles);
	}

	protected void addTestCasesRegExp(String toolchain, String settings, String[] regExp) {

		File toolchainFile = getToolchainFile(toolchain);
		File settingsFile = getSettingsFile(settings);
		File trunk = new File(TestUtil.getPathFromTrunk("/"));
		Collection<File> testFiles = TestUtil.getFilesRegex(trunk, regExp);
		addTestCases(toolchainFile, settingsFile, testFiles);
	}

	protected void addTestCases(String toolchain, String settings,
			DirectoryFileEndingsPair[] directoryFileEndingsPairs) {
		File toolchainFile = getToolchainFile(toolchain);
		File settingsFile = getSettingsFile(settings);
		Collection<File> testFiles = new ArrayList<File>();
		for (DirectoryFileEndingsPair directoryFileEndingsPair : directoryFileEndingsPairs) {
			testFiles.addAll(getInputFiles(directoryFileEndingsPair.getDirectory(),
					directoryFileEndingsPair.getFileEndings(), directoryFileEndingsPair.getLimit()));
		}
		addTestCases(toolchainFile, settingsFile, testFiles);
	}

	/**
	 * Get input files from directory. Do not take all files but only up to n pseudorandomly selected files.
	 */
	private Collection<File> getInputFiles(String directory, String[] fileEndings, int n) {
		final List<File> files = TestUtil.getFiles(new File(TestUtil.getPathFromTrunk(directory)), fileEndings);
		return TestUtil.limitFiles(files, n);
	}

	public static class DirectoryFileEndingsPair {
		private final String mDirectory;
		private final String[] mFileEndings;
		private final int mLimit;

		public DirectoryFileEndingsPair(String directory, String[] fileEndings) {
			super();
			mDirectory = directory;
			mFileEndings = fileEndings;
			mLimit = Integer.MAX_VALUE;
		}

		public DirectoryFileEndingsPair(String directory, String[] fileEndings, int limit) {
			super();
			mDirectory = directory;
			mFileEndings = fileEndings;
			mLimit = limit;
		}

		public String getDirectory() {
			return mDirectory;
		}

		public String[] getFileEndings() {
			return mFileEndings;
		}

		public int getLimit() {
			return mLimit;
		}
	}
}
