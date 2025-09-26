/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.regressiontest.generic;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.List;
import java.util.Map;

import org.yaml.snakeyaml.Yaml;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition.NamedServiceCallback;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.decider.ChcTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.expectedresult.IExpectedResultFinder;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.ChcOverallResult;
import de.uni_freiburg.informatik.ultimate.test.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestLogfile;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;

public class SleepThreadModularChcTestSuite extends UltimateTestSuite {
	private static final String TOOLCHAIN = "examples/concurrent/bpl/parameterized/ThreadModularVerifier.xml";
	private static final String DIRECTORY = "examples/concurrent/bpl/parameterized/";
	private static final String TASKDEF_REGEX = ".*/regression/.*\\.yml";
	private static final int DEFAULT_TIMEOUT = 600;

	@Override
	protected Collection<UltimateTestCase> createTestCases() {
		final File toolchainFile = UltimateRunDefinitionGenerator.getFileFromTrunkDir(TOOLCHAIN);

		final Collection<File> selectedYamlFiles = TestUtil.getFilesRegex(
				UltimateRunDefinitionGenerator.getFileFromTrunkDir(DIRECTORY), new String[] { TASKDEF_REGEX });

		final List<UltimateTestCase> result = new ArrayList<>();
		for (final var taskDefFile : selectedYamlFiles) {
			final var taskDefinition = parseTaskDefinition(taskDefFile);

			final String bplFilename = (String) taskDefinition.get("input_files");
			final Path bplPath = taskDefFile.toPath().getParent().resolve(bplFilename);

			final Path settingsFile = getSettingsFile(taskDefinition, taskDefFile.toPath().getParent());

			long timeout = getTimeout(taskDefinition);
			if (timeout > 10_000L) { // TODO remove
				timeout = 10_000L;
			}

			final var urd = new UltimateRunDefinition(bplPath.toFile(), settingsFile.toFile(), toolchainFile, timeout,
					applySettings(taskDefFile, taskDefinition));

			final String name = taskDefFile.getParentFile().getParentFile().getName() + "__" + taskDefFile.getName();
			result.add(new TestCase(constructITestResultDecider(urd, taskDefinition), urd, List.of(), name));
		}
		result.sort(Comparator.comparing(UltimateTestCase::getName));

		return result;
	}

	private static Map<String, Object> parseTaskDefinition(final File taskDefFile) {
		try (var stream = new FileInputStream(taskDefFile)) {
			return new Yaml().load(stream);
		} catch (final IOException e) {
			throw new AssertionError(e);
		}
	}

	private static ITestResultDecider constructITestResultDecider(final UltimateRunDefinition ultimateRunDefinition,
			final Map<String, Object> taskDefinition) {
		return new ChcTestResultDecider(ultimateRunDefinition, false) {
			@Override
			public IExpectedResultFinder<ChcOverallResult> constructExpectedResultFinder() {
				return new ExpectedResultFinder(taskDefinition);
			}
		};
	}

	private static class ExpectedResultFinder implements IExpectedResultFinder<ChcOverallResult> {
		private final ExpectedResultFinderStatus mStatus;
		private final ChcOverallResult mExpected;

		public ExpectedResultFinder(final Map<String, Object> taskDefinition) {
			@SuppressWarnings("unchecked")
			final var propertyDef = ((Collection<Map<String, Object>>) taskDefinition.get("properties")).stream()
					.filter(propEntry -> ((String) propEntry.get("property_file")).endsWith("unreach-call.prp"))
					.findFirst();
			if (propertyDef.isEmpty()) {
				mStatus = ExpectedResultFinderStatus.NO_EXPECTED_RESULT_FOUND;
				mExpected = null;
			} else {
				final var expected = propertyDef.get().get("expected_verdict").toString();
				switch (expected) {
				case "sat":
				case "true":
					mExpected = ChcOverallResult.SAT;
					mStatus = ExpectedResultFinderStatus.EXPECTED_RESULT_FOUND;
					break;
				case "unsat":
					mExpected = ChcOverallResult.UNSAT;
					mStatus = ExpectedResultFinderStatus.EXPECTED_RESULT_FOUND;
					break;
				case "unknown":
					mExpected = ChcOverallResult.UNKNOWN;
					mStatus = ExpectedResultFinderStatus.EXPECTED_RESULT_FOUND;
					break;
				default:
					mExpected = null;
					mStatus = ExpectedResultFinderStatus.NO_EXPECTED_RESULT_FOUND;
				}
			}
		}

		@Override
		public void findExpectedResult(final UltimateRunDefinition ultimateRunDefinition) {
			// already done in constructor
		}

		@Override
		public ExpectedResultFinderStatus getExpectedResultFinderStatus() {
			return mStatus;
		}

		@Override
		public String getExpectedResultFinderMessage() {
			return mExpected.toString();
		}

		@Override
		public ChcOverallResult getExpectedResult() {
			return mExpected;
		}
	}

	@Override
	protected ITestSummary[] constructTestSummaries() {
		return new ITestSummary[0];
	}

	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		return new IIncrementalLog[0];
	}

	@SuppressWarnings("unchecked")
	private static Path getSettingsFile(final Map<String, Object> taskDefinition, final Path currentDirectory) {
		if (taskDefinition.containsKey("options")) {
			final var options = (Map<String, Object>) taskDefinition.get("options");
			if (options.containsKey("settings_file")) {
				final String epfFilename = (String) options.get("settings_file");
				final Path settingsFile = currentDirectory.resolve(epfFilename);
				if (!Files.exists(settingsFile)) {
					throw new IllegalStateException("Settings file does not exist: " + settingsFile);
				}
				return settingsFile;
			}
		}
		throw new IllegalStateException("No settings file specified");
	}

	@SuppressWarnings("unchecked")
	private static long getTimeout(final Map<String, Object> taskDefinition) {
		if (taskDefinition.containsKey("options")) {
			final var options = (Map<String, Object>) taskDefinition.get("options");
			if (options.containsKey("timeout")) {
				return (int) options.get("timeout") * 1000L;
			}
		}
		return DEFAULT_TIMEOUT * 1000L;
	}

	@SuppressWarnings("unchecked")
	private NamedServiceCallback applySettings(final File taskDefFile, final Map<String, Object> taskDefinition) {
		final var options = (Map<String, Object>) taskDefinition.get("options");
		if (options == null) {
			return null;
		}
		final String[] pluginIds = options.keySet().stream()
				.filter(s -> s.startsWith("de.uni_freiburg.informatik.ultimate")).toArray(String[]::new);
		return new NamedServiceCallback(taskDefFile.getName(), services -> {
			final var layer = services.registerPreferenceLayer(getClass(), pluginIds);
			for (final var plugin : pluginIds) {
				final var preferences = layer.getPreferenceProvider(plugin);
				for (final var entry : ((Map<String, Object>) options.get(plugin)).entrySet()) {
					final Object value;
					if (entry.getValue() instanceof Map || entry.getValue() instanceof List) {
						value = new Yaml().dump(entry.getValue());
					} else {
						value = entry.getValue();
					}
					preferences.put(entry.getKey(), value);
				}
			}
			return layer;
		});
	}

	private static final class TestCase extends UltimateTestCase {
		private final String mName;

		public TestCase(final ITestResultDecider decider, final UltimateRunDefinition urd,
				final List<ITestLogfile> logs, final String name) {
			super(decider, urd, logs);
			mName = name;
		}

		@Override
		public String getName() {
			return mName;
		}
	}
}
