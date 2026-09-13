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
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition.NamedServiceCallback;
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

/** Fails on invalid expectations or when an expected-unsafe program is reported safe. */
public class SifaThreadModularRegressionSoundnessTest extends AbstractTraceAbstractionTestSuite {

	private static final String TOOLCHAIN = "SifaThreadModular.xml";
	private static final String SETTINGS = "examples/concurrent/bpl/regression/thread-modular-sifa/testSettings.epf";
	private static final String INPUT_DIR = "examples/concurrent/bpl/regression/thread-modular-sifa";
	private static final String FILE_ENDING = ".bpl";
	private static final String EXCLUDE_REGEX = ".*/scaling/.*";
	private static final long TIMEOUT_MS = 30_000L;
	private static final String INTERFERENCE_METHOD = "STRONGEST_POSTCONDITION";

	private static final NamedServiceCallback RUN_CONFIGURATION =
			new NamedServiceCallback(INTERFERENCE_METHOD, services -> {
				services.getPreferenceProvider("de.uni_freiburg.informatik.ultimate.plugins.sifa")
						.put("Interference Applicator", INTERFERENCE_METHOD);
				return services;
			});

	@Override
	protected long getTimeout() {
		return TIMEOUT_MS;
	}

	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition ultimateRunDefinition) {
		return new UnsoundnessOnlySafetyCheckTestResultDecider(ultimateRunDefinition);
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		final List<File> inputFiles = selectInputFiles();
		final File toolchainFile = UltimateRunDefinitionGenerator.getFileFromToolchainDir(TOOLCHAIN);
		final File settingsFile = UltimateRunDefinitionGenerator.getFileFromTrunkDir(SETTINGS);
		final long timeout = getTimeout();
		for (final File inputFile : inputFiles) {
			addTestCase(new UltimateRunDefinition(inputFile, settingsFile, toolchainFile, timeout, RUN_CONFIGURATION));
		}
		return super.createTestCases();
	}

	private static List<File> selectInputFiles() {
		final File inputDir = UltimateRunDefinitionGenerator.getFileFromTrunkDir(INPUT_DIR);
		final List<File> inputFiles = TestUtil.getFiles(inputDir, FILE_ENDING).stream()
				.filter(file -> !file.getAbsolutePath().matches(EXCLUDE_REGEX))
				.sorted((a, b) -> a.getAbsolutePath().compareTo(b.getAbsolutePath()))
				.collect(Collectors.toList());
		if (inputFiles.isEmpty()) {
			throw new IllegalStateException("No " + FILE_ENDING + " test inputs found in " + inputDir);
		}
		return inputFiles;
	}

	private static final class UnsoundnessOnlySafetyCheckTestResultDecider extends SafetyCheckTestResultDecider {
		UnsoundnessOnlySafetyCheckTestResultDecider(final UltimateRunDefinition ultimateRunDefinition) {
			super(ultimateRunDefinition, true);
		}

		@Override
		public ITestResultEvaluation<SafetyCheckerOverallResult> constructTestResultEvaluation() {
			return new UnsoundnessOnlyEvaluation();
		}
	}

	/** Accepts conservative results, but rejects invalid expectations and unsound safe results. */
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
				mTestResult = TestResult.FAIL;
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
