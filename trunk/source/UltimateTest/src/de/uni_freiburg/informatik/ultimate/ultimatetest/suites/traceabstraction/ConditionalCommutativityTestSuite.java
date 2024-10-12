/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
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

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.function.UnaryOperator;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.PartialOrderReductionFacade.OrderType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.ConComChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.ConComCheckerCriterion;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition.NamedServiceCallback;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;

/**
 * @author klumpp@informatik.uni-freiburg.de
 *
 */
public class ConditionalCommutativityTestSuite extends AbstractTraceAbstractionTestSuite {
	private static final int TIMEOUT = 30; // seconds

	private static final String TOOLCHAIN_C = "AutomizerCInline.xml";
	private static final String TOOLCHAIN_BPL = "AutomizerBplInline.xml";

	// @formatter:off
	private static final String[] BASE_SETTINGS = {
		"gemcutter/NewStatesSleep.epf",
		"gemcutter/NewStatesSleepPersistentFixedOrder.epf"
	};
	// @formatter:on

	// @formatter:off
	private static final List<Map<String, Object>> VARIANTS = List.of(
		interpolantApproach()
	);
	// @formatter:on

	// @formatter:off
	private static final String[] BENCHMARKS_BPL = {
		"examples/concurrent/bpl/conditional_commutativity/"
	};
	private static final String[] BENCHMARKS_C = {
	};
	// @formatter:on

	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition urd) {
		return new SafetyCheckTestResultDecider(urd, false);
	}

	@Override
	public long getTimeout() {
		return TIMEOUT * 1000L;
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final var setting : BASE_SETTINGS) {
			for (final var variant : VARIANTS) {
				final var namedCallback = new NamedServiceCallback("IA", overwriteSettings(variant));
				addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionFromTrunk(BENCHMARKS_C,
						new String[] { ".c" }, setting, TOOLCHAIN_C, getTimeout(), namedCallback));
				addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionFromTrunk(BENCHMARKS_BPL,
						new String[] { ".bpl" }, setting, TOOLCHAIN_BPL, getTimeout(), namedCallback));
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

	private static Map<String, Object> interpolantApproach() {
		return Map.of(
		// @formatter:off
			TraceAbstractionPreferenceInitializer.LABEL_POR_DFS_ORDER, OrderType.LOOP_LOCKSTEP,
			TraceAbstractionPreferenceInitializer.LABEL_CON_COM_CHECKER, ConComChecker.IA,
			TraceAbstractionPreferenceInitializer.LABEL_CON_COM_CHECKER_CRITERION, ConComCheckerCriterion.DEFAULT
		// @formatter:on
		);
	}
}
