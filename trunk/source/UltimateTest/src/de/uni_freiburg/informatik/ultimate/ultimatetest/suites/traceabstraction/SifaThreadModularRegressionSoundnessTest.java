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
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.UnaryOperator;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
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
	private static final String PROP_METHODS = "sifa.regression.methods";
	private static final String PROP_LOCATION_TRACKING_MODE = "sifa.regression.locationTrackingMode";
	private static final String PROP_USE_BUCKETS = "sifa.regression.useBuckets";
	private static final String PROP_MAX_BUCKETS = "sifa.regression.maxBuckets";
	private static final String PROP_MAX_DISJUNCTS_PER_BUCKET = "sifa.regression.maxDisjunctsPerBucket";
	private static final String PROP_LOCKSET_AWARE = "sifa.regression.locksetAware";
	private static final String PROP_PUBLISH_ON_ACQUIRE = "sifa.regression.publishOnAcquire";
	private static final String PROP_PUBLISH_DEBUG = "sifa.regression.publishDebug";
	private static final String PROP_JOIN_PRECISION = "sifa.regression.joinPrecision";
	private static final String PROP_MAX_PARALLEL_EXPLICIT_VALUES = "sifa.regression.maxParallelExplicitValues";
	private static final String PROP_ABSTRACT_DOMAIN = "sifa.regression.abstractDomain";
	private static final String PROP_COMPOUND_DOMAINS = "sifa.regression.compoundDomains";
	private static final String PROP_MAX_PARALLEL_INTERVALS = "sifa.regression.maxParallelIntervals";
	private static final String PROP_MAX_PARALLEL_OCTAGON = "sifa.regression.maxParallelOctagon";
	private static final String PROP_LOCATION_ABSTRACTION = "sifa.regression.locationAbstraction";
	private static final String PROP_MAX_DISJUNCTIONS = "sifa.regression.maxDisjunctions";
	private static final String PROP_INNER_WIDENING_THRESHOLD = "sifa.regression.innerWideningThreshold";
	private static final String PROP_OUTER_WIDENING_THRESHOLD = "sifa.regression.outerWideningThreshold";

	private static final String TOOLCHAIN = "SifaThreadModular.xml";
	private static final String SETTINGS = "examples/concurrent/bpl/regression/thread-modular-sifa/testSettings.epf";
	private static final String INPUT_DIR = "examples/concurrent/bpl/regression/thread-modular-sifa";
	private static final String FILE_ENDING = ".bpl";
	private static final String EXCLUDE_REGEX = ".*/scaling/.*";
	private static final long TIMEOUT_MS = 30_000L;

	/*
	 * Central comparison configuration.
	 *
	 * Change these constants when you want a different experiment, then rerun
	 * /Users/dk/run_sifa_comparison.sh.
	 *
	 * Useful method sets:
	 * - Full comparison:
	 *   { "STRONGEST_POSTCONDITION", "PREPOST", "GUARDED_EXACT_UPDATE", "POST_STATE", "UNARY_GLOBALS", "NONE" }
	 * - Sound methods only:
	 *   { "STRONGEST_POSTCONDITION", "PREPOST", "GUARDED_EXACT_UPDATE", "POST_STATE", "UNARY_GLOBALS" }
	 * - Minimal fast comparison:
	 *   { "POST_STATE", "UNARY_GLOBALS", "NONE" }
	 */
	// private static final String[] METHODS = { "STRONGEST_POSTCONDITION", "PREPOST", "GUARDED_EXACT_UPDATE", "POST_STATE", "UNARY_GLOBALS", "NONE" };
	private static final String[] METHODS = { "STRONGEST_POSTCONDITION" };

	// private static final String ABSTRACT_DOMAIN = "ExplicitValueDomain";
	// Alternatives:
	// private static final String ABSTRACT_DOMAIN = "IntervalDomain";
	// private static final String ABSTRACT_DOMAIN = "EqDomain";
	private static final String ABSTRACT_DOMAIN = "OctagonDomain";
	// private static final String ABSTRACT_DOMAIN = "CompoundDomain";
	private static final String FLUID = "SizeLimitFluid";
	private static final int MAX_PARALLEL_EXPLICIT_VALUES = 2;
	private static final int MAX_PARALLEL_OCTAGON = 1;
	private static final int MAX_DISJUNCTIONS = 8;
	private static final boolean JOIN_PRECISION = true;
	private static final boolean USE_BUCKETS = true;
	private static final boolean LOCKSET_AWARE = false;
	private static final boolean PUBLISH_ON_ACQUIRE = false;
	private static final boolean PROOF_CHECK = false;
	private static final boolean RESULT_PRINT = true;

	// private static final String LOCATION_ABSTRACTION = "SPLIT_AT_GUARD_AND_EXIT";
	// private static final String LOCATION_ABSTRACTION = "SINGLETON";
	// private static final String LOCATION_ABSTRACTION = "SPLIT_AT_GUARD";
	private static final String LOCATION_ABSTRACTION = "SPLIT_AT_GUARDS_AND_WRITES";
	// private static final String LOCATION_ABSTRACTION = "SPLIT_AT_EVERY_LOCATION";

	@Override
	protected long getTimeout() {
		return Long.getLong(PROP_TIMEOUT_MS, TIMEOUT_MS);
	}

	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition ultimateRunDefinition) {
		return new UnsoundnessOnlySafetyCheckTestResultDecider(ultimateRunDefinition);
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		final List<File> inputFiles = selectInputFiles();
		final File toolchainFile = resolveToolchainFile();
		final File settingsFile = resolveTrunkOrAbsoluteFile(getSettingsPath());

		for (final String method : getMethods()) {
			final UnaryOperator<IUltimateServiceProvider> callback = s -> {
				final var prefs = s.getPreferenceProvider("de.uni_freiburg.informatik.ultimate.plugins.sifa");
				prefs.put("Interference Applicator", method);

				// Apply common experiment settings. Change the constants above to adjust runs.
				final String locationTrackingMode = System.getProperty(PROP_LOCATION_TRACKING_MODE);
				if (locationTrackingMode != null && !locationTrackingMode.isBlank()) {
					prefs.put("Location Tracking Mode", locationTrackingMode);
				}
				prefs.put("Abstract Domain", System.getProperty(PROP_ABSTRACT_DOMAIN, ABSTRACT_DOMAIN));
				final String compoundDomains = System.getProperty(PROP_COMPOUND_DOMAINS);
				if (compoundDomains != null && !compoundDomains.isBlank()) {
					prefs.put("CompoundDomain Intern Domains", compoundDomains);
				}
				prefs.put("Fluid", FLUID);
				prefs.put("Max. Parallel Explicit Values",
						Integer.getInteger(PROP_MAX_PARALLEL_EXPLICIT_VALUES, MAX_PARALLEL_EXPLICIT_VALUES));
				final Integer maxParallelIntervals = Integer.getInteger(PROP_MAX_PARALLEL_INTERVALS);
				if (maxParallelIntervals != null) {
					prefs.put("Max. Parallel Intervals", maxParallelIntervals);
				}
				prefs.put("Max. Parallel Octagon",
						Integer.getInteger(PROP_MAX_PARALLEL_OCTAGON, MAX_PARALLEL_OCTAGON));
				prefs.put("Join Precision", Boolean.parseBoolean(
						System.getProperty(PROP_JOIN_PRECISION, Boolean.toString(JOIN_PRECISION))));
				prefs.put("Use Buckets", Boolean.parseBoolean(
							System.getProperty(PROP_USE_BUCKETS, Boolean.toString(USE_BUCKETS))));
				putIntegerIfPresent(prefs, "Max. Buckets", PROP_MAX_BUCKETS);
				putIntegerIfPresent(prefs, "Max. Disjuncts per Bucket", PROP_MAX_DISJUNCTS_PER_BUCKET);
				prefs.put("Lockset-Aware Interference", Boolean.parseBoolean(
						System.getProperty(PROP_LOCKSET_AWARE, Boolean.toString(LOCKSET_AWARE))));
				prefs.put("Publish On Acquire", Boolean.parseBoolean(
						System.getProperty(PROP_PUBLISH_ON_ACQUIRE, Boolean.toString(PUBLISH_ON_ACQUIRE))));
				putBooleanIfPresent(prefs, "Publish Debug", PROP_PUBLISH_DEBUG);
				prefs.put("Proof Check", PROOF_CHECK);
				prefs.put("Result Print", RESULT_PRINT);
				prefs.put("Location Abstraction",
						System.getProperty(PROP_LOCATION_ABSTRACTION, LOCATION_ABSTRACTION));
				prefs.put("SizeLimitFluid Max. Disjunctions",
						Integer.getInteger(PROP_MAX_DISJUNCTIONS, MAX_DISJUNCTIONS));
				final Integer innerWideningThreshold = Integer.getInteger(PROP_INNER_WIDENING_THRESHOLD);
				if (innerWideningThreshold != null) {
					prefs.put("Inner Interference Widening Threshold", innerWideningThreshold);
				}
				final Integer outerWideningThreshold = Integer.getInteger(PROP_OUTER_WIDENING_THRESHOLD);
				if (outerWideningThreshold != null) {
					prefs.put("Outer Interference Widening Threshold", outerWideningThreshold);
				}

				return s;
			};
			addTestCases(toolchainFile, settingsFile, inputFiles, method, callback);
		}
		return super.createTestCases();
	}

	private static void putIntegerIfPresent(final IPreferenceProvider prefs, final String preferenceLabel,
			final String propertyName) {
		final Integer value = Integer.getInteger(propertyName);
		if (value != null) {
			prefs.put(preferenceLabel, value);
		}
	}

	private static void putBooleanIfPresent(final IPreferenceProvider prefs, final String preferenceLabel,
			final String propertyName) {
		final String value = System.getProperty(propertyName);
		if (value != null && !value.isBlank()) {
			prefs.put(preferenceLabel, Boolean.parseBoolean(value));
		}
	}

	private void addTestCases(final File toolchainFile, final File settingsFile, final Collection<File> inputFiles,
			final String name, final UnaryOperator<IUltimateServiceProvider> callback) {
		final long timeout = getTimeout();
		final NamedServiceCallback serviceCallback = new NamedServiceCallback(name, callback);
		for (final File inputFile : inputFiles) {
			addTestCase(new UltimateRunDefinition(inputFile, settingsFile, toolchainFile, timeout, serviceCallback));
		}
	}

	private static List<File> selectInputFiles() {
		final File inputDir = resolveTrunkOrAbsoluteFile(getInputDir());
		final String includeRegex = System.getProperty(PROP_INCLUDE_REGEX);
		final String excludeRegex = System.getProperty(PROP_EXCLUDE_REGEX, EXCLUDE_REGEX);
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

	private static String[] getMethods() {
		final String configured = System.getProperty(PROP_METHODS);
		if (configured == null || configured.isBlank()) {
			return METHODS;
		}
		return Arrays.stream(configured.split(",")).map(String::trim).filter(s -> !s.isEmpty())
				.toArray(String[]::new);
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
