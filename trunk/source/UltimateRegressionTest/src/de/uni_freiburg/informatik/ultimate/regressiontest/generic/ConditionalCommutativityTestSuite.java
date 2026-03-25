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

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.function.UnaryOperator;

import org.yaml.snakeyaml.Yaml;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.PartialOrderReductionFacade.OrderType;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.SemanticIndependenceRelation.IndependenceConditions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.test.AbstractModelCheckerTestSuite;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition.NamedServiceCallback;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author klumpp@informatik.uni-freiburg.de
 *
 */
public class ConditionalCommutativityTestSuite extends AbstractModelCheckerTestSuite {
	private static final int TIMEOUT = 60; // seconds

	private static final String SKIPPED_TESTS_FILE = "examples/concurrent/conditional_commutativity/.testignore";

	private static final String TOOLCHAIN_C = "AutomizerCInline.xml";
	private static final String TOOLCHAIN_BPL = "AutomizerBplInline.xml";

	private Map<String, List<Map<String, String>>> mIgnoredTests;

	// @formatter:off
	private static final String[] BASE_SETTINGS = {
		//"gemcutter/NewStatesSleep.epf",
		"gemcutter/NewStatesSleepPersistentFixedOrder.epf"
	};
	// @formatter:on

	// @formatter:off
	private static final List<Pair<String, Map<String, Object>>> VARIANTS = List.of(
		//counterExampleApproach(),
		//counterExampleApproachWithContext(),
		counterExampleApproachWithSymbolic(),
		counterExampleApproachWithSymbolicSimplified()
	);
	// @formatter:on

	// @formatter:off
	private static final String[] BENCHMARKS_BPL = {
		"examples/concurrent/conditional_commutativity/"
	};
	private static final String[] BENCHMARKS_C = {
		"examples/concurrent/conditional_commutativity/"
	};
	// @formatter:on

	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition urd) {
		final String overriddenVerdict = getSkipVerdict(urd);
		if (overriddenVerdict == null) {
			return new SafetyCheckTestResultDecider(urd, false);
		}
		return new SafetyCheckTestResultDecider(urd, false, overriddenVerdict);
	}

	@Override
	protected ITestSummary[] constructTestSummaries() {
		return new ITestSummary[0];
	}

	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		return new IIncrementalLog[0];
	}

	@Override
	public long getTimeout() {
		return TIMEOUT * 1000L;
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		try {
			mIgnoredTests = new Yaml()
					.load(new FileInputStream(UltimateRunDefinitionGenerator.getFileFromTrunkDir(SKIPPED_TESTS_FILE)));
		} catch (final FileNotFoundException e) {
			// No tests to ignore
			mIgnoredTests = Map.of();
		}

		for (final var setting : BASE_SETTINGS) {
			for (final var variant : VARIANTS) {
				final var callback = new NamedServiceCallback(variant.getKey(), overwriteSettings(variant.getValue()));
				/*
				 * addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionFromTrunk(BENCHMARKS_C, new String[] {
				 * ".c" }, setting, TOOLCHAIN_C, getTimeout(), callback));
				 */
				addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionFromTrunk(BENCHMARKS_BPL,
						new String[] { ".bpl" }, setting, TOOLCHAIN_BPL, getTimeout(), callback));
			}
		}
		return super.createTestCases();
	}

	private static UnaryOperator<IUltimateServiceProvider> overwriteSettings(final Map<String, Object> settings) {
		return services -> {
			final IUltimateServiceProvider overlay =
					services.registerPreferenceLayer(ConditionalCommutativityTestSuite.class, Activator.PLUGIN_ID);
			final IPreferenceProvider prefProvider = overlay.getPreferenceProvider(Activator.PLUGIN_ID);
			for (final var entry : settings.entrySet()) {
				prefProvider.put(entry.getKey(), entry.getValue());
			}
			return overlay;
		};
	}

	private static Pair<String, Map<String, Object>> counterExampleApproach() {
		return new Pair<>("CE", Map.of(
		// @formatter:off
			TraceAbstractionPreferenceInitializer.LABEL_POR_DFS_ORDER, OrderType.LOOP_LOCKSTEP,
			TraceAbstractionPreferenceInitializer.LABEL_COMMUTATIVITY_COND_SYNTHESIS, IndependenceConditions.SUFFICIENT
		// @formatter:on
		));
	}

	private static Pair<String, Map<String, Object>> counterExampleApproachWithContext() {
		return new Pair<>("CE+Ctx", Map.of(
		// @formatter:off
			TraceAbstractionPreferenceInitializer.LABEL_POR_DFS_ORDER, OrderType.LOOP_LOCKSTEP,
			TraceAbstractionPreferenceInitializer.LABEL_COMMUTATIVITY_COND_SYNTHESIS, IndependenceConditions.SUFFICIENT_WITH_CONTEXT
		// @formatter:on
		));
	}

	private static Pair<String, Map<String, Object>> counterExampleApproachWithSymbolic() {
		return new Pair<>("CE+Symb", Map.of(
		// @formatter:off
			TraceAbstractionPreferenceInitializer.LABEL_POR_DFS_ORDER, OrderType.LOOP_LOCKSTEP,
			TraceAbstractionPreferenceInitializer.LABEL_COMMUTATIVITY_COND_SYNTHESIS, IndependenceConditions.NECESSARY_AND_SUFFICIENT
		// @formatter:on
		));
	}

	private static Pair<String, Map<String, Object>> counterExampleApproachWithSymbolicSimplified() {
		return new Pair<>("CE+Symb", Map.of(
		// @formatter:off
			TraceAbstractionPreferenceInitializer.LABEL_POR_DFS_ORDER, OrderType.LOOP_LOCKSTEP,
			TraceAbstractionPreferenceInitializer.LABEL_COMMUTATIVITY_COND_SYNTHESIS, IndependenceConditions.NECESSARY_AND_SUFFICIENT,
			TraceAbstractionPreferenceInitializer.LABEL_COMMUTATIVITY_COND_SIMPLIFIER, true
		// @formatter:on
		));
	}

	private String getSkipVerdict(final UltimateRunDefinition urd) {
		for (final var taskSet : mIgnoredTests.entrySet()) {
			for (final var task : taskSet.getValue()) {
				if (urd.getInput()[0].getName().equals(task.get("task"))
						&& urd.getSettings().getName().equals(task.get("settings"))
						&& urd.getToolchain().getName().equals(task.get("toolchain"))
						&& urd.getServiceCallback().getName().equals(task.get("callback"))) {
					return taskSet.getKey();
				}
			}
		}
		return null;
	}
}
