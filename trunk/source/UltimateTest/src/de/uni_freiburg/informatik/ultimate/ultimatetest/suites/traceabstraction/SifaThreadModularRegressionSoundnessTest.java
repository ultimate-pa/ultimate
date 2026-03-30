/*
 * Copyright (C) 2026 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.traceabstraction;

import java.io.File;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimate.test.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.ThreeTierTestResultDecider.ITestResultEvaluation;
import de.uni_freiburg.informatik.ultimate.test.decider.expectedresult.IExpectedResultFinder;
import de.uni_freiburg.informatik.ultimate.test.decider.expectedresult.IExpectedResultFinder.ExpectedResultFinderStatus;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.IOverallResultEvaluator;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.SafetyCheckerOverallResult;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;

/** Only fails on unsoundness: expected-unsafe reported as safe. */
public class SifaThreadModularRegressionSoundnessTest extends AbstractTraceAbstractionTestSuite {

	private static final String PROP_TIMEOUT_MS = "sifa.regression.timeout.ms";
	private static final String PROP_MAX_FILES = "sifa.regression.maxFiles";
	private static final String PROP_INCLUDE_REGEX = "sifa.regression.includeRegex";
	private static final String PROP_EXCLUDE_REGEX = "sifa.regression.excludeRegex";
	private static final String PROP_TOOLCHAIN = "sifa.regression.toolchain";
	private static final String PROP_SETTINGS = "sifa.regression.settings";
	private static final String PROP_INPUT_DIR = "sifa.regression.inputDir";
	private static final String PROP_FILE_ENDING = "sifa.regression.fileEnding";

	private static final String TOOLCHAIN = "SifaThreadModular.xml";
	private static final String SETTINGS = "examples/concurrent/bpl/regression/thread-modular-sifa/testSettings.epf";
	private static final String INPUT_DIR = "examples/concurrent/bpl/regression";
	private static final String FILE_ENDING = ".bpl";
	private static final long TIMEOUT_MS = 30_000L;

	@Override
	protected long getTimeout() {
		return Long.getLong(PROP_TIMEOUT_MS, TIMEOUT_MS);
	}

	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition ultimateRunDefinition) {
		return new UnsoundnessOnlySafetyCheckTestResultDecider(ultimateRunDefinition);
	}

	@Override
	public java.util.Collection<UltimateTestCase> createTestCases() {
		final List<File> inputFiles = selectInputFiles();
		addTestCases(resolveToolchainFile(), resolveTrunkOrAbsoluteFile(getSettingsPath()), inputFiles);
		return super.createTestCases();
	}

	private static List<File> selectInputFiles() {
		final File inputDir = resolveTrunkOrAbsoluteFile(getInputDir());
		final String includeRegex = System.getProperty(PROP_INCLUDE_REGEX);
		final String excludeRegex = System.getProperty(PROP_EXCLUDE_REGEX);
		final int maxFiles = Integer.getInteger(PROP_MAX_FILES, -1);

		List<File> inputFiles = TestUtil.getFiles(inputDir, getFileEnding()).stream()
						.sorted((a, b) -> a.getAbsolutePath().compareTo(b.getAbsolutePath()))
						.collect(Collectors.toList());

		if (includeRegex != null && !includeRegex.isBlank()) {
			inputFiles = inputFiles.stream().filter(f -> f.getAbsolutePath().matches(includeRegex))
					.collect(Collectors.toList());
		}
		if (excludeRegex != null && !excludeRegex.isBlank()) {
			inputFiles = inputFiles.stream().filter(f -> !f.getAbsolutePath().matches(excludeRegex))
					.collect(Collectors.toList());
		}
		if (maxFiles >= 0 && inputFiles.size() > maxFiles) {
			inputFiles = inputFiles.subList(0, maxFiles);
		}
		return inputFiles;
	}

	private static File resolveToolchainFile() {
		final String toolchain = System.getProperty(PROP_TOOLCHAIN, TOOLCHAIN);
		final File direct = new File(toolchain);
		if (direct.isAbsolute()) {
			return direct;
		}
		return UltimateRunDefinitionGenerator.getFileFromToolchainDir(toolchain);
	}

	private static File resolveTrunkOrAbsoluteFile(final String path) {
		final File direct = new File(path);
		if (direct.isAbsolute()) {
			return direct;
		}
		return UltimateRunDefinitionGenerator.getFileFromTrunkDir(path);
	}

	private static String getSettingsPath() {
		return System.getProperty(PROP_SETTINGS, SETTINGS);
	}

	private static String getInputDir() {
		return System.getProperty(PROP_INPUT_DIR, INPUT_DIR);
	}

	private static String getFileEnding() {
		return System.getProperty(PROP_FILE_ENDING, FILE_ENDING);
	}

	private static final class UnsoundnessOnlySafetyCheckTestResultDecider extends SafetyCheckTestResultDecider {
		UnsoundnessOnlySafetyCheckTestResultDecider(final UltimateRunDefinition ultimateRunDefinition) {
			super(ultimateRunDefinition, true);
		}

		@Override
		public IExpectedResultFinder<SafetyCheckerOverallResult> constructExpectedResultFinder() {
			return new FirstlinePreferredExpectedResultFinder();
		}

		@Override
		public ITestResultEvaluation<SafetyCheckerOverallResult> constructTestResultEvaluation() {
			return new UnsoundnessOnlyEvaluation();
		}
	}

	/** Uses first-line annotation, falls back to filename keywords. */
	private static final class FirstlinePreferredExpectedResultFinder
			implements IExpectedResultFinder<SafetyCheckerOverallResult> {
		private ExpectedResultFinderStatus mStatus;
		private String mMessage;
		private SafetyCheckerOverallResult mExpectedResult;

		@Override
		public void findExpectedResult(final UltimateRunDefinition ultimateRunDefinition) {
			final Set<SafetyCheckerOverallResult> expectedResults = new HashSet<>();
			for (final File file : ultimateRunDefinition.getInput()) {
				final SafetyCheckerOverallResult expected = determineExpectedResult(file);
				if (expected != null) {
					expectedResults.add(expected);
				}
			}

			if (expectedResults.isEmpty()) {
				mStatus = ExpectedResultFinderStatus.NO_EXPECTED_RESULT_FOUND;
				mExpectedResult = null;
				mMessage = "No #annotation and no filename keyword matched";
				return;
			}
			if (expectedResults.size() > 1) {
				mStatus = ExpectedResultFinderStatus.ERROR;
				mExpectedResult = null;
				mMessage = "Conflicting expected results across input files: " + expectedResults;
				return;
			}
			mStatus = ExpectedResultFinderStatus.EXPECTED_RESULT_FOUND;
			mExpectedResult = expectedResults.iterator().next();
			mMessage = "Expected result: " + mExpectedResult;
		}

		@Override
		public ExpectedResultFinderStatus getExpectedResultFinderStatus() {
			return mStatus;
		}

		@Override
		public String getExpectedResultFinderMessage() {
			return mMessage;
		}

		@Override
		public SafetyCheckerOverallResult getExpectedResult() {
			return mExpectedResult;
		}

		private static SafetyCheckerOverallResult determineExpectedResult(final File file) {
			final String firstLine = TestUtil.extractFirstLine(file);
			final SafetyCheckerOverallResult fromFirstLine =
					findBySubstring(firstLine, TestUtil.constructFirstlineKeywordMap_SafetyChecker());
			if (fromFirstLine != null) {
				return fromFirstLine;
			}
			return findByRegex(file.getName(), TestUtil.constructFilenameKeywordMap_AllSafetyChecker());
		}

		private static SafetyCheckerOverallResult findBySubstring(final String text,
				final Map<String, SafetyCheckerOverallResult> keywordMap) {
			if (text == null) {
				return null;
			}
			final Set<SafetyCheckerOverallResult> matches = new HashSet<>();
			for (final var entry : keywordMap.entrySet()) {
				if (text.contains(entry.getKey())) {
					matches.add(entry.getValue());
				}
			}
			if (matches.size() == 1) {
				return matches.iterator().next();
			}
			return null;
		}

		private static SafetyCheckerOverallResult findByRegex(final String text,
				final Map<String, SafetyCheckerOverallResult> keywordMap) {
			if (text == null) {
				return null;
			}
			final Set<SafetyCheckerOverallResult> matches = new HashSet<>();
			for (final var entry : keywordMap.entrySet()) {
				if (text.matches(entry.getKey())) {
					matches.add(entry.getValue());
				}
			}
			if (matches.size() == 1) {
				return matches.iterator().next();
			}
			return null;
		}
	}

	/** Fails only when expected-unsafe is reported safe. */
	private static final class UnsoundnessOnlyEvaluation implements ITestResultEvaluation<SafetyCheckerOverallResult> {
		private String mCategory;
		private String mMessage;
		private TestResult mTestResult;

		@Override
		public void evaluateTestResult(final IExpectedResultFinder<SafetyCheckerOverallResult> expectedResultFinder,
				final IOverallResultEvaluator<SafetyCheckerOverallResult> overallResultDeterminer) {
			final ExpectedResultFinderStatus status = expectedResultFinder.getExpectedResultFinderStatus();
			final SafetyCheckerOverallResult actual = overallResultDeterminer.getOverallResult();
			mCategory = actual + " (" + status + ")";
			mMessage = "Expected: " + expectedResultFinder.getExpectedResultFinderMessage() + " | Actual: "
					+ overallResultDeterminer.generateOverallResultMessage();

			if (status != ExpectedResultFinderStatus.EXPECTED_RESULT_FOUND) {
				mTestResult = TestResult.UNKNOWN;
				return;
			}

			final SafetyCheckerOverallResult expected = expectedResultFinder.getExpectedResult();
			final boolean expectedUnsafe = expected == SafetyCheckerOverallResult.UNSAFE
					|| expected == SafetyCheckerOverallResult.UNSAFE_DEREF
					|| expected == SafetyCheckerOverallResult.UNSAFE_FREE
					|| expected == SafetyCheckerOverallResult.UNSAFE_MEMTRACK
					|| expected == SafetyCheckerOverallResult.UNSAFE_OVERAPPROXIMATED;
			final boolean actualSafe = actual == SafetyCheckerOverallResult.SAFE
					|| actual == SafetyCheckerOverallResult.VALID_ANNOTATION;

			if (expectedUnsafe && actualSafe) {
				mTestResult = TestResult.FAIL;
				mCategory = actual + " (Expected:" + expected + ")";
				mMessage = "Unsound result: expected unsafe but got safe.";
				return;
			}

			mTestResult = TestResult.UNKNOWN;
		}

		@Override
		public void evaluateTestResult(final IExpectedResultFinder<SafetyCheckerOverallResult> expectedResultFinder,
				final Throwable e) {
			mCategory = "EXCEPTION_OR_ERROR (" + expectedResultFinder.getExpectedResultFinderStatus() + ")";
			mMessage = "Exception during run: " + e.getMessage();
			mTestResult = TestResult.UNKNOWN;
		}

		@Override
		public TestResult getTestResult() {
			return mTestResult;
		}

		@Override
		public String getTestResultCategory() {
			return mCategory;
		}

		@Override
		public String getTestResultMessage() {
			return mMessage;
		}
	}
}
