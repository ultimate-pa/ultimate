/*
 * Copyright (C) 2025 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2025 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.regressiontest.AbstractRegressionTestSuite;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimate.test.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SafetyCheckTestResultDecider.SafetyCheckerTestResultEvaluation;
import de.uni_freiburg.informatik.ultimate.test.decider.expectedresult.IExpectedResultFinder;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.IOverallResultEvaluator;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.SafetyCheckerOverallResult;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 *
 * This test suite automatically generates test cases from the example folder. First the verification and the generation
 * of witnesses is tested, afterwards the validation of the previously generated witnesses.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class WitnessRegressionTestSuite extends AbstractRegressionTestSuite {
	// Be careful: These fields have to match the settings for WitnessPrinter
	private static final String WITNESS_SUFFIX = "-witness";
	private static final List<String> WITNESS_EXTENSIONS = List.of(".graphml", ".yml");

	private static final long DEFAULT_TIMEOUT = 25 * 1000L;

	public WitnessRegressionTestSuite() {
		mTimeout = DEFAULT_TIMEOUT;
		mRootFolder = TestUtil.getPathFromTrunk("examples/witness-generation-validation");
	}

	@Override
	protected ITestResultDecider getTestResultDecider(final UltimateRunDefinition runDefinition) {
		return new WitnessSafetyCheckTestResultDecider(runDefinition);
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		final List<UltimateTestCase> generation = new ArrayList<>();
		final List<UltimateTestCase> validation = new ArrayList<>();
		for (final UltimateTestCase t : super.createTestCases()) {
			final UltimateRunDefinition def = t.getUltimateRunDefinition();
			final String toolchainName = def.getToolchain().getName().toLowerCase();
			if (toolchainName.contains("generation")) {
				generation.add(t);
			} else if (toolchainName.contains("validation")) {
				for (final File f : def.getInput()) {
					for (final String ending : WITNESS_EXTENSIONS) {
						final File witness = new File(f.getAbsolutePath() + WITNESS_SUFFIX + ending);
						final File[] newFiles = DataStructureUtils.concat(def.getInput(), new File[] { witness });
						final UltimateRunDefinition newDef = new UltimateRunDefinition(newFiles, def.getSettings(),
								def.getToolchain(), def.getTimeout());
						validation.add(new UltimateTestCase(getTestResultDecider(def), newDef, List.of()));
					}
				}
			} else {
				throw new AssertionError("Not supported yet.");
			}
		}
		return DataStructureUtils.concat(generation, validation);
	}

	public class WitnessSafetyCheckTestResultDecider extends SafetyCheckTestResultDecider {
		public WitnessSafetyCheckTestResultDecider(final UltimateRunDefinition ultimateRunDefinition) {
			super(ultimateRunDefinition, false);
		}

		@Override
		public ITestResultEvaluation<SafetyCheckerOverallResult> constructTestResultEvaluation() {
			return new WitnessSafetyCheckerTestResultEvaluation();
		}
	}

	public class WitnessSafetyCheckerTestResultEvaluation extends SafetyCheckerTestResultEvaluation {
		public WitnessSafetyCheckerTestResultEvaluation() {
			super(null);
		}

		@Override
		public void evaluateTestResult(final IExpectedResultFinder<SafetyCheckerOverallResult> expectedResultFinder,
				final IOverallResultEvaluator<SafetyCheckerOverallResult> overallResultDeterminer) {
			// WORKAROUND: Validation with Referee yields VALID_ANNOTATION instead of SAFE. Therefore, we consider this
			// also as succes in order not to crash.
			if (overallResultDeterminer.getOverallResult() == SafetyCheckerOverallResult.VALID_ANNOTATION) {
				mTestResult = TestResult.SUCCESS;
				mMessage = "UltimateResult: " + SafetyCheckerOverallResult.VALID_ANNOTATION;
				mCategory = SafetyCheckerOverallResult.VALID_ANNOTATION.toString();
			} else {
				super.evaluateTestResult(expectedResultFinder, overallResultDeterminer);
			}
		}
	}
}
