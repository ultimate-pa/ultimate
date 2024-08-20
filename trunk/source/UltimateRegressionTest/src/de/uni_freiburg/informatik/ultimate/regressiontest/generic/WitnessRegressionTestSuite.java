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
package de.uni_freiburg.informatik.ultimate.regressiontest.generic;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.regressiontest.AbstractRegressionTestSuite;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.expectedresult.IExpectedResultFinder;
import de.uni_freiburg.informatik.ultimate.test.decider.expectedresult.KeywordBasedExpectedResultFinder;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.SafetyCheckerOverallResult;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 *
 * This test suite automatically generates test cases from the example folder. If you place input files, toolchains and
 * settings files in a folder named regression, they will automatically be picked up.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class WitnessRegressionTestSuite extends AbstractRegressionTestSuite {
	private static final List<String> WITNESS_EXTENSIONS = List.of(".graphml", ".yaml", ".yml");
	private static final long DEFAULT_TIMEOUT = 25 * 1000L;

	public WitnessRegressionTestSuite() {
		mTimeout = DEFAULT_TIMEOUT;
		mRootFolder = TestUtil.getPathFromTrunk("examples/witness-checking");
	}

	@Override
	protected ITestResultDecider getTestResultDecider(final UltimateRunDefinition runDefinition,
			final String overridenExpectedVerdict) {
		checkNoOverridenVerdict(overridenExpectedVerdict);
		return new WitnessSafetyCheckTestResultDecider(runDefinition);
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		final List<UltimateTestCase> result = new ArrayList<>();
		for (final UltimateTestCase t : super.createTestCases()) {
			final UltimateRunDefinition def = t.getUltimateRunDefinition();
			for (final File f : def.getInput()) {
				final File[] witnesses = f.getParentFile().listFiles(
						(d, n) -> WITNESS_EXTENSIONS.stream().anyMatch(n::endsWith) && n.startsWith(f.getName()));
				for (final File witness : witnesses) {
					final File[] newFiles = DataStructureUtils.concat(def.getInput(), new File[] { witness });
					final UltimateRunDefinition newDef = new UltimateRunDefinition(newFiles, def.getSettings(),
							def.getToolchain(), def.getTimeout());
					result.add(new UltimateTestCase(getTestResultDecider(def, null), newDef, List.of(), null));
				}
			}
		}
		return result;
	}

	private static final class WitnessSafetyCheckTestResultDecider extends SafetyCheckTestResultDecider {
		public WitnessSafetyCheckTestResultDecider(final UltimateRunDefinition ultimateRunDefinition) {
			super(ultimateRunDefinition, false);
		}

		@Override
		public IExpectedResultFinder<SafetyCheckerOverallResult> constructExpectedResultFinder() {
			// Determine the expected result, based on the subfolders correctness/violation
			return new KeywordBasedExpectedResultFinder<>(null, Map.of("correctness", SafetyCheckerOverallResult.SAFE,
					"violation", SafetyCheckerOverallResult.UNSAFE), null);
		}
	}

}
