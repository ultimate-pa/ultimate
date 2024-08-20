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
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.stream.Collectors;

import org.yaml.snakeyaml.Yaml;

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
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;

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
	private static final String SKIPPED_FILENAME = "skip.yml";

	protected long mTimeout;
	protected String mRootFolder;
	/**
	 * Regex that excludes toolchain files whose path is matched by the regex.
	 */
	protected String mExcludeFilterRegexToolchain;
	/**
	 * Regex that includes only toolchain files whose path is matched by the regex.
	 */
	protected String mIncludeFilterRegexToolchain;
	/**
	 * Regex that excludes settings files whose path is matched by the regex.
	 */
	protected String mExcludeFilterRegexSettings;
	/**
	 * Regex that includes only settings files whose path is matched by the regex.
	 */
	protected String mIncludeFilterRegexSettings;
	/**
	 * Regex that excludes input files whose path is matched by the regex.
	 */
	protected String mExcludeFilterRegexInput;
	/**
	 * Regex that includes only input files whose path is matched by the regex.
	 */
	protected String mIncludeFilterRegexInput;
	protected String[] mFiletypesToConsider;

	public AbstractRegressionTestSuite() {
		mTimeout = 1000;
		mExcludeFilterRegexToolchain = "";
		mExcludeFilterRegexInput = "";
		mExcludeFilterRegexSettings = "";
		mIncludeFilterRegexToolchain = "";
		mIncludeFilterRegexInput = "";
		mIncludeFilterRegexSettings = "";
		mFiletypesToConsider = new String[] { ".c", ".bpl", ".i", ".ats" };
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		final List<UltimateTestCase> rtr = new ArrayList<>();

		final Collection<Config> runConfigurations = getRunConfiguration();
		final Predicate<File> filesRegexFilter = getFilesRegexFilter();
		for (final Config runConfiguration : runConfigurations) {
			final Collection<File> inputFiles = getInputFiles(filesRegexFilter, runConfiguration);
			final NestedMap3<File, String, String, String> skippedTests = getSkippedTests(inputFiles);
			for (final File inputFile : inputFiles) {
				final UltimateRunDefinition urd =
						new UltimateRunDefinition(inputFile, runConfiguration.getSettingsFile(),
								runConfiguration.getToolchainFile(), getTimeout(runConfiguration, inputFile));
				final String overridenVerdict = skippedTests.get(inputFile,
						runConfiguration.getSettingsFile().getName(), runConfiguration.getToolchainFile().getName());
				rtr.add(buildTestCase(urd, getTestResultDecider(urd, overridenVerdict)));
			}
		}
		return rtr;
	}

	/**
	 * Collect all tests that should be marked as skipped. To do so, all files with SKIPPED_FILENAME next to
	 * {@code inputFiles} are considered and a NestedMap3 is extracted from.
	 */
	private static NestedMap3<File, String, String, String> getSkippedTests(final Collection<File> inputFiles) {
		final NestedMap3<File, String, String, String> result = new NestedMap3<>();
		inputFiles.stream().map(x -> new File(x.getParentFile(), SKIPPED_FILENAME)).distinct()
				.forEach(x -> addSkippedTest(x, result));
		return result;
	}

	private static void addSkippedTest(final File ignoreFile, final NestedMap3<File, String, String, String> map) {
		try {
			final Map<String, List<Map<String, String>>> parsed = new Yaml().load(new FileInputStream(ignoreFile));
			for (final var entry : parsed.entrySet()) {
				for (final Map<String, String> triples : entry.getValue()) {
					if (triples.values().stream().anyMatch(x -> x.contains("/"))) {
						throw new UnsupportedOperationException("Invalid filename in ignore-file" + ignoreFile
								+ ". The filename may only contain a name, not a relative path. "
								+ "Add a new ignore-file next to the task itself (if desired).");
					}
					map.put(new File(ignoreFile.getParentFile(), triples.get("task")), triples.get("settings"),
							triples.get("toolchain"), entry.getKey());
				}
			}
		} catch (final FileNotFoundException e) {
			// File does not exist, nothing to be ignored
		}
	}

	protected long getTimeout(final Config rundef, final File file) {
		return mTimeout;
	}

	/**
	 * Get a collection of toolchain/settings pairs of which the settings name starts with the toolchains name (without
	 * ending) or vice versa.
	 *
	 * @param regexFilter
	 *
	 * @return A collection of {@link Config}s of files. The first file represents a toolchain and the second represents
	 *         settings.
	 */
	protected Collection<Config> getRunConfiguration() {
		final File root = getRootFolder(mRootFolder);
		if (root == null) {
			return Collections.emptySet();
		}

		final Predicate<File> tcRegexFilter = getToolchainRegexFilter();
		final Predicate<File> settingsRegexFilter = getSettingsRegexFilter();
		final List<File> tcAndSettingsFiles = TestUtil.getFiles(root, ".xml", ".epf");

		final Collection<File> toolchainFiles =
				tcAndSettingsFiles.stream().filter(FILTER_XML.and(tcRegexFilter)).collect(Collectors.toSet());
		final Collection<File> settingsFiles =
				tcAndSettingsFiles.stream().filter(FILTER_EPF.and(settingsRegexFilter)).collect(Collectors.toSet());

		if (toolchainFiles.isEmpty() || settingsFiles.isEmpty()) {
			return Collections.emptySet();
		}

		final Set<Config> rtr = new HashSet<>();
		for (final File toolchain : toolchainFiles) {
			final String toolchainName = toolchain.getName().replaceAll("\\..*", "");
			final String localRegex = Matcher.quoteReplacement(toolchain.getParent()) + ".*";

			final Collection<File> relevantSettings = TestUtil.filterFiles(settingsFiles, localRegex);

			for (final File settings : relevantSettings) {
				final String settingsName = settings.getName().replaceAll("\\..*", "");

				if (settingsName.startsWith(toolchainName) || toolchainName.startsWith(settingsName)) {
					rtr.add(new Config(toolchain, settings));
				}
			}
		}

		return rtr;
	}

	private Predicate<File> getSettingsRegexFilter() {
		return getRegexFilter(new String[] { ".*regression.*", mIncludeFilterRegexSettings },
				new String[] { mExcludeFilterRegexSettings });
	}

	private Predicate<File> getToolchainRegexFilter() {
		return getRegexFilter(new String[] { ".*regression.*", mIncludeFilterRegexToolchain },
				new String[] { mExcludeFilterRegexToolchain });
	}

	private Predicate<File> getFilesRegexFilter() {
		return getRegexFilter(new String[] { mIncludeFilterRegexInput }, new String[] { mExcludeFilterRegexInput });
	}

	private static String[] removeEmptyOrNull(final String[] str) {
		if (str == null || str.length == 0) {
			return str;
		}
		final List<String> rtr = Arrays.stream(str).filter(a -> a != null && !a.isEmpty()).collect(Collectors.toList());
		return rtr.toArray(new String[rtr.size()]);
	}

	private static Predicate<File> getRegexFilter(final String[] include, final String[] exclude) {
		final String[] filteredInclude = removeEmptyOrNull(include);
		final String[] filteredExclude = removeEmptyOrNull(exclude);
		if (filteredExclude == null || filteredExclude.length == 0) {
			return TestUtil.getRegexTest(filteredInclude);
		}
		return TestUtil.getRegexTest(filteredInclude).and(TestUtil.getRegexTest(filteredExclude).negate());
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
	protected Collection<File> getInputFiles(final Predicate<File> regexFilter, final Config runConfiguration) {
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

	protected abstract ITestResultDecider getTestResultDecider(UltimateRunDefinition runDefinition,
			String overridenExpectedVerdict);

	protected void checkNoOverridenVerdict(final String overridenExpectedVerdict) {
		if (overridenExpectedVerdict != null) {
			throw new UnsupportedOperationException(getClass().getSimpleName() + " does not support skipping tests.");
		}
	}

	public static final class Config
			extends de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair<File, File> {

		public Config(final File toolchain, final File settings) {
			super(toolchain, settings);
		}

		public File getToolchainFile() {
			return getFirst();
		}

		public File getSettingsFile() {
			return getSecond();
		}

		@Override
		public String toString() {
			return "Toolchain:" + getToolchainFile() + " Settings:" + getSettingsFile();
		}
	}

}
