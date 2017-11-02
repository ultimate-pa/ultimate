/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Regression Test Library.
 *
 * The ULTIMATE Regression Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Regression Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Regression Test Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Regression Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Regression Test Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.regressiontest;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.logs.incremental.IncrementalLogWithBenchmarkResults;
import de.uni_freiburg.informatik.ultimate.test.logs.incremental.IncrementalLogWithVMParameters;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.TraceAbstractionTestSummary;
import de.uni_freiburg.informatik.ultimate.test.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;

/**
 * An {@link AbstractRegressionTestSuite} is a {@link UltimateTestSuite} that automatically generates tests from folders
 * named <code>regression</code>. For all toolchain and settings file combinations where the toolchain name is a prefix
 * of the settings file or the settings file name is a prefix of the toolchain filename, test cases are generated for
 * all files in the folder and all subfolders where the deepest of both (toolchain and settings file) is located.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class AbstractRegressionTestSuite extends UltimateTestSuite {

	private static final Predicate<File> FILTER_XML = TestUtil.getFileEndingTest(".xml");
	private static final Predicate<File> FILTER_EPF = TestUtil.getFileEndingTest(".epf");

	protected long mTimeout;
	protected String mRootFolder;
	protected String mExcludeFilterRegex;
	protected String mIncludeFilterRegex;
	protected String mFileExcludeFilterRegex;
	protected String mFileIncludeFilterRegex;
	protected String[] mFiletypesToConsider;

	public AbstractRegressionTestSuite() {
		super();
		mTimeout = 1000;
		mExcludeFilterRegex = "";
		mIncludeFilterRegex = "";
		mFileExcludeFilterRegex = "";
		mFileIncludeFilterRegex = "";
		mFiletypesToConsider = new String[] { ".c", ".bpl", ".i", ".ats" };
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		final List<UltimateTestCase> rtr = new ArrayList<>();

		final Collection<Pair> runConfigurations = getRunConfiguration();
		final Predicate<File> filesRegexFilter = getFilesRegexFilter();
		for (final Pair runConfiguration : runConfigurations) {
			final Collection<File> inputFiles = getInputFiles(filesRegexFilter, runConfiguration);

			for (final File inputFile : inputFiles) {
				final UltimateRunDefinition urd = new UltimateRunDefinition(inputFile,
						runConfiguration.getSettingsFile(), runConfiguration.getToolchainFile(), mTimeout);
				final String name = String.format("%s+%s: %s", runConfiguration.getToolchainFile().getName(),
						runConfiguration.getSettingsFile().getName(), inputFile.getAbsolutePath());
				rtr.add(buildTestCase(urd, getTestResultDecider(urd), name));
			}
		}
		return rtr;
	}

	/**
	 * Get a collection of toolchain/settings pairs of which the settings name starts with the toolchains name (without
	 * ending) or vice versa.
	 *
	 * @param regexFilter
	 *
	 * @return A collection of {@link Pair}s of files. The first file represents a toolchain and the second represents
	 *         settings.
	 */
	protected Collection<Pair> getRunConfiguration() {
		final Set<Pair> rtr = new HashSet<>();

		final File root = getRootFolder(mRootFolder);
		if (root == null) {
			return rtr;
		}

		final Predicate<File> regexFilter = getToolchainSettingsRegexFilter();
		final List<File> tcAndSettingsFiles = TestUtil.getFiles(root, new String[] { ".xml", ".epf" });

		final Collection<File> toolchainFiles =
				tcAndSettingsFiles.stream().filter(FILTER_XML.and(regexFilter)).collect(Collectors.toSet());
		final Collection<File> settingsFiles =
				tcAndSettingsFiles.stream().filter(FILTER_EPF.and(regexFilter)).collect(Collectors.toSet());

		for (final File toolchain : toolchainFiles) {
			final String toolchainName = toolchain.getName().replaceAll("\\..*", "");
			final String localRegex = Matcher.quoteReplacement(toolchain.getParent()) + ".*";

			final Collection<File> relevantSettings = TestUtil.filterFiles(settingsFiles, localRegex);

			for (final File settings : relevantSettings) {
				final String settingsName = settings.getName().replaceAll("\\..*", "");

				if (settingsName.startsWith(toolchainName) || toolchainName.startsWith(settingsName)) {
					rtr.add(new Pair(toolchain, settings));
				}
			}
		}

		return rtr;
	}

	private Predicate<File> getToolchainSettingsRegexFilter() {
		final List<String> regexes = new ArrayList<>();
		regexes.add(".*regression.*");
		if (!mIncludeFilterRegex.isEmpty()) {
			regexes.add(mIncludeFilterRegex);
		}
		Predicate<File> regexFilter;
		if (!mExcludeFilterRegex.isEmpty()) {
			regexFilter = TestUtil.getRegexTest(regexes).and(TestUtil.getRegexTest(mExcludeFilterRegex).negate());
		} else {
			regexFilter = TestUtil.getRegexTest(regexes);
		}
		return regexFilter;
	}

	private Predicate<File> getFilesRegexFilter() {
		final List<String> regexes = new ArrayList<>();
		if (!mFileIncludeFilterRegex.isEmpty()) {
			regexes.add(mFileIncludeFilterRegex);
		}
		Predicate<File> regexFilter;
		if (!mFileExcludeFilterRegex.isEmpty()) {
			regexFilter = TestUtil.getRegexTest(regexes).and(TestUtil.getRegexTest(mFileExcludeFilterRegex).negate());
		} else {
			regexFilter = TestUtil.getRegexTest(regexes);
		}
		return regexFilter;
	}

	@Override
	protected ITestSummary[] constructTestSummaries() {
		if (createLogs()) {
			return new ITestSummary[] { new TraceAbstractionTestSummary(this.getClass()) };
		}
		return new ITestSummary[0];
	}

	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		if (createLogs()) {
			return new IIncrementalLog[] { new IncrementalLogWithBenchmarkResults(this.getClass()),
					new IncrementalLogWithVMParameters(this.getClass(), mTimeout) };
		}
		return new IIncrementalLog[0];
	}

	/**
	 * @return true if you want to create standard summaries and logs for our regression test suite, false otherwise.
	 */
	protected boolean createLogs() {
		return false;
	}

	/***
	 *
	 * @return null if the path to the folder is invalid, a File representing the path otherwise
	 */
	protected static File getRootFolder(final String path) {
		if (path == null) {
			return null;
		}

		final File root = new File(path);

		if (!root.exists() || !root.isDirectory()) {
			return null;
		}

		return root;
	}

	/**
	 * @param regexFilter
	 * @return All the files that should be used in this test suite. The default implementation uses all files that can
	 *         be found recursively under the folder in which the deeper file (settings or toolchain, specified in
	 *         runConfiguration) lies and that have the endings specified by mFileTypesToConsider.
	 */
	protected Collection<File> getInputFiles(final Predicate<File> regexFilter, final Pair runConfiguration) {
		final File tcParent = runConfiguration.getToolchainFile().getParentFile();
		final File settingParent = runConfiguration.getSettingsFile().getParentFile();
		final File parent;
		if (settingParent.toString().startsWith(tcParent.toString())) {
			parent = settingParent;
		} else {
			parent = tcParent;
		}
		return TestUtil.getFiles(parent, mFiletypesToConsider).stream().filter(regexFilter)
				.collect(Collectors.toList());
	}

	protected abstract ITestResultDecider getTestResultDecider(UltimateRunDefinition runDefinition);

	public static final class Pair {

		private final File mToolchainFile;
		private final File mSettingsFile;

		public Pair(final File toolchain, final File settings) {
			mToolchainFile = toolchain;
			mSettingsFile = settings;
		}

		public File getToolchainFile() {
			return mToolchainFile;
		}

		public File getSettingsFile() {
			return mSettingsFile;
		}

		@Override
		public String toString() {
			return "Toolchain:" + getToolchainFile() + " Settings:" + getSettingsFile();
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + (mSettingsFile == null ? 0 : mSettingsFile.hashCode());
			result = prime * result + (mToolchainFile == null ? 0 : mToolchainFile.hashCode());
			return result;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final Pair other = (Pair) obj;
			if (mSettingsFile == null) {
				if (other.mSettingsFile != null) {
					return false;
				}
			} else if (!mSettingsFile.equals(other.mSettingsFile)) {
				return false;
			}
			if (mToolchainFile == null) {
				if (other.mToolchainFile != null) {
					return false;
				}
			} else if (!mToolchainFile.equals(other.mToolchainFile)) {
				return false;
			}
			return true;
		}

	}

}
