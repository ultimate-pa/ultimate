/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 École Polytechnique
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

import java.util.Collection;
import java.util.Map;
import java.util.function.UnaryOperator;

import de.uni_freiburg.informatik.ultimate.civlizer.Activator;
import de.uni_freiburg.informatik.ultimate.civlizer.preferences.CivlizerPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.AbstractModelCheckerTestSuite;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition.NamedServiceCallback;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.CivlTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;

public class CivlizerTestSuite extends AbstractModelCheckerTestSuite {
	private static final String CIVLIZER_CIVL_COMMAND_PROPERTY = "civlizer.test.civl.command";
	private static final int TIMEOUT = 20; // seconds
	private static final String TOOLCHAIN_BPL = "AutomizerCivlizerBpl.xml";

	// @formatter:off
	private static final String[] BENCHMARKS_BPL = {
		"examples/concurrent/bpl/civlizer/"
	};
	// @formatter:on

	// @formatter:off
	private static final String[] BASE_SETTINGS = {
		"AutomizerCivlizerBpl.epf"
	};
	// @formatter:on

	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition runDefinition) {
		return new CivlTestResultDecider(runDefinition);
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
		for (final var setting : BASE_SETTINGS) {
			final var callback =
					new NamedServiceCallback("EnableCivlRunner", overwriteSettings(localCivlRunnerSettings()));
			addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionFromTrunk(BENCHMARKS_BPL,
					new String[] { ".bpl" }, setting, TOOLCHAIN_BPL, getTimeout(), callback));
		}
		return super.createTestCases();
	}

	private static UnaryOperator<IUltimateServiceProvider> overwriteSettings(final Map<String, Object> settings) {
		return services -> {
			final IUltimateServiceProvider overlay =
					services.registerPreferenceLayer(CivlizerTestSuite.class, Activator.PLUGIN_ID);
			final IPreferenceProvider prefProvider = overlay.getPreferenceProvider(Activator.PLUGIN_ID);
			for (final var entry : settings.entrySet()) {
				prefProvider.put(entry.getKey(), entry.getValue());
			}
			return overlay;
		};
	}

	private static Map<String, Object> localCivlRunnerSettings() {
		return Map.of(
		// @formatter:off
			CivlizerPreferenceInitializer.LABEL_RUN_CIVL_ON_OUTPUT, true,
			CivlizerPreferenceInitializer.LABEL_CIVL_COMMAND, System.getProperty(CIVLIZER_CIVL_COMMAND_PROPERTY)
		// @formatter:on
		);
	}
}
