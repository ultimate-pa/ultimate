/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE ViewAbstractionTest Library.
 *
 * The ULTIMATE ViewAbstractionTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ViewAbstractionTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ViewAbstractionTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ViewAbstractionTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ViewAbstractionTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.test;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import org.yaml.snakeyaml.Yaml;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition.NamedServiceCallback;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.expectedresult.IExpectedResultFinder;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.SafetyCheckerOverallResult;
import de.uni_freiburg.informatik.ultimate.test.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;

public class ViewAbstractionTestSuite extends UltimateTestSuite {
	private static final String SETTINGS = "ViewAbstractionBpl.epf";
	private static final String TOOLCHAIN = "ViewAbstractionBpl.xml";
	private static final String DIRECTORY = "examples/concurrent/bpl/parameterized/";
	private static final String TASKDEF_REGEX = ".*\\.viewabs\\.yml";
	private static final int DEFAULT_TIMEOUT = 30;

	@Override
	protected Collection<UltimateTestCase> createTestCases() {
		final File toolchainFile = UltimateRunDefinitionGenerator.getFileFromToolchainDir(TOOLCHAIN);
		final File settingsFile = UltimateRunDefinitionGenerator.getFileFromSettingsDir(SETTINGS);
		final Collection<File> selectedYamlFiles = TestUtil.getFilesRegex(
				UltimateRunDefinitionGenerator.getFileFromTrunkDir(DIRECTORY), new String[] { TASKDEF_REGEX });

		final List<UltimateTestCase> result = new ArrayList<>();
		for (final var taskDefFile : selectedYamlFiles) {
			final var taskDefinition = parseTaskDefinition(taskDefFile);
			final String bplFilename = (String) taskDefinition.get("input_files");
			final String bplPath = taskDefFile.getParent() + System.getProperty("file.separator") + bplFilename;

			final var urd = new UltimateRunDefinition(new File(bplPath), settingsFile, toolchainFile,
					getTimeout(taskDefinition), applySettings(taskDefFile, taskDefinition));
			result.add(new UltimateTestCase(constructITestResultDecider(urd, taskDefinition), urd, List.of()));
		}

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
		return new SafetyCheckTestResultDecider(ultimateRunDefinition, false) {
			@Override
			public IExpectedResultFinder<SafetyCheckerOverallResult> constructExpectedResultFinder() {
				return new ExpectedResultFinder(taskDefinition);
			}
		};
	}

	private static class ExpectedResultFinder implements IExpectedResultFinder<SafetyCheckerOverallResult> {
		private final ExpectedResultFinderStatus mStatus;
		private final SafetyCheckerOverallResult mExpected;

		public ExpectedResultFinder(final Map<String, Object> taskDefinition) {
			final var propertyDef = ((Collection<Map<String, Object>>) taskDefinition.get("properties")).stream()
					.filter(propEntry -> ((String) propEntry.get("property_file")).endsWith("unreach-call.prp"))
					.findFirst();
			if (propertyDef.isEmpty()) {
				mStatus = ExpectedResultFinderStatus.NO_EXPECTED_RESULT_FOUND;
				mExpected = null;
			} else {
				final var expected = propertyDef.get().get("expected_verdict").toString();
				switch (expected) {
				case "true":
					mExpected = SafetyCheckerOverallResult.SAFE;
					mStatus = ExpectedResultFinderStatus.EXPECTED_RESULT_FOUND;
					break;
				case "false":
					mExpected = SafetyCheckerOverallResult.UNSAFE;
					mStatus = ExpectedResultFinderStatus.EXPECTED_RESULT_FOUND;
					break;
				case "unknown":
					mExpected = SafetyCheckerOverallResult.UNKNOWN;
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
		public SafetyCheckerOverallResult getExpectedResult() {
			return mExpected;
		}
	}

	@Override
	protected ITestSummary[] constructTestSummaries() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		// TODO Auto-generated method stub
		return null;
	}

	private long getTimeout(final Map<String, Object> taskDefinition) {
		if (taskDefinition.containsKey("options")) {
			final var options = (Map<String, Object>) taskDefinition.get("options");
			if (options.containsKey("timeout")) {
				return (long) options.get("timeout") * 1000L;
			}
		}
		return DEFAULT_TIMEOUT * 1000L;
	}

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
					preferences.put(entry.getKey(), entry.getValue());
				}
			}
			return layer;
		});
	}
}
