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
import java.util.regex.Matcher;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateStarter;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
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

	protected long mTimeout;
	protected String mRootFolder;
	protected String mFilterRegex;
	protected String[] mFiletypesToConsider;

	public AbstractRegressionTestSuite() {
		mTimeout = 1000;
		mFilterRegex = ".*";
		mFiletypesToConsider = new String[] { ".c", ".bpl", ".i",  ".ats" };
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		final List<UltimateTestCase> rtr = new ArrayList<>();
		final Collection<Pair> runConfigurations = getRunConfiguration();

		for (final Pair runConfiguration : runConfigurations) {
			final Collection<File> inputFiles = getInputFiles(runConfiguration);

			for (final File inputFile : inputFiles) {
				final UltimateRunDefinition urd = new UltimateRunDefinition(inputFile,
						runConfiguration.getSettingsFile(), runConfiguration.getToolchainFile());
				final UltimateStarter starter = new UltimateStarter(urd, mTimeout);
				rtr.add(new UltimateTestCase(
						String.format("%s+%s: %s", runConfiguration.getToolchainFile().getName(),
								runConfiguration.getSettingsFile().getName(), inputFile.getAbsolutePath()),
						getTestResultDecider(urd), starter, urd, null, null));
			}
		}
		return rtr;
	}

	/**
	 * Get a collection of toolchain/settings pairs of which the settings name starts with the toolchains name (without
	 * ending) or vice versa.
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

		Collection<File> toolchainFiles = TestUtil.getFiles(root, new String[] { ".xml" });
		Collection<File> settingsFiles = TestUtil.getFiles(root, new String[] { ".epf" });

		toolchainFiles = TestUtil.filterFiles(toolchainFiles, ".*regression.*");
		toolchainFiles = TestUtil.filterFiles(toolchainFiles, mFilterRegex);
		settingsFiles = TestUtil.filterFiles(settingsFiles, ".*regression.*");
		settingsFiles = TestUtil.filterFiles(settingsFiles, mFilterRegex);

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

	@Override
	protected ITestSummary[] constructTestSummaries() {
		return new ITestSummary[0];
	}

	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		return new IIncrementalLog[0];
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
	 * @return All the files that should be used in this test suite. The default implementation uses all files that can
	 *         be found recursively under the folder in which the Toolchain file (specified in runConfiguration) lies
	 *         and that have the endings specified by mFileTypesToConsider.
	 */
	protected Collection<File> getInputFiles(final Pair runConfiguration) {
		return TestUtil.getFiles(runConfiguration.getToolchainFile().getParentFile(), mFiletypesToConsider);
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
			result = prime * result + ((mSettingsFile == null) ? 0 : mSettingsFile.hashCode());
			result = prime * result + ((mToolchainFile == null) ? 0 : mToolchainFile.hashCode());
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
