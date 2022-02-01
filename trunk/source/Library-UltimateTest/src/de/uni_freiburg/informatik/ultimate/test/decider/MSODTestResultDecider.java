/*
 * Copyright (C) 2019 Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Nico Hauff (hauffn@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE UnitTest Library.
 *
 * The ULTIMATE UnitTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE UnitTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE UnitTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE UnitTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE UnitTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.test.decider;

import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.decider.expectedresult.IExpectedResultFinder;
import de.uni_freiburg.informatik.ultimate.test.decider.expectedresult.SMTLibExpectedResultFinder;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.IOverallResultEvaluator;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.MSODOverallResultEvaluator;

/**
 * @author hauffn@informatik.uni-freiburg.de
 * @author henkele@informatik.uni-freiburg.de
 */
public class MSODTestResultDecider extends ThreeTierTestResultDecider<LBool> {
	public MSODTestResultDecider(final UltimateRunDefinition ultimateRunDefinition,
			final boolean unknownIsJUnitSuccess) {
		super(ultimateRunDefinition, unknownIsJUnitSuccess);
	}

	@Override
	public IExpectedResultFinder<LBool> constructExpectedResultFinder() {
		return new SMTLibExpectedResultFinder<>(LBool.UNKNOWN, LBool.SAT, LBool.UNSAT);
	}

	@Override
	public IOverallResultEvaluator<LBool> constructUltimateResultEvaluation() {
		return new MSODOverallResultEvaluator();
	}

	@Override
	public ITestResultEvaluation<LBool> constructTestResultEvaluation() {
		return new MSODTestResultEvaluator();
	}

	private class MSODTestResultEvaluator implements ITestResultEvaluation<LBool> {
		private TestResult mTestResult;
		private String mCategory;
		private String mMessage;

		@Override
		public void evaluateTestResult(final IExpectedResultFinder<LBool> expectedResultEvaluation,
				final IOverallResultEvaluator<LBool> overallResultDeterminer) {

			final LBool expected = expectedResultEvaluation.getExpectedResult();
			final LBool actual = overallResultDeterminer.getOverallResult();

			if (expected == null) {
				mTestResult = TestResult.UNKNOWN;
				mCategory = "UNKNOWN";

			} else if (expected.equals(actual)) {
				mTestResult = TestResult.SUCCESS;
				mCategory = "SUCCESS";

			} else {
				mTestResult = TestResult.FAIL;
				mCategory = "FAIL";
			}

			mMessage = "expected: " + expected + " actual: " + actual;
		}

		@Override
		public void evaluateTestResult(final IExpectedResultFinder<LBool> expectedResultEvaluation, final Throwable e) {
			mTestResult = TestResult.FAIL;

			if (e == null) {
				mCategory = "EmptyException";
				mMessage = mCategory;
			} else {
				mCategory = e.getClass().toString();
				mMessage = e.getMessage();
			}
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
