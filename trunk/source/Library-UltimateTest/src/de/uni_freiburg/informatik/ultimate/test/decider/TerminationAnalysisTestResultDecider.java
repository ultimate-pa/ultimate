/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.decider.expectedresult.IExpectedResultFinder;
import de.uni_freiburg.informatik.ultimate.test.decider.expectedresult.KeywordBasedExpectedResultFinder;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.IOverallResultEvaluator;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.TerminationAnalysisOverallResult;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.TerminationAnalysisOverallResultEvaluator;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;

/**
 * Use keywords in filename and first line to decide correctness of termination
 * analysis result.
 * This class is largely copy and paste from SafetyCheckTestResultDecider.
 * Maybe we can write a good superclass for both.
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class TerminationAnalysisTestResultDecider extends
		ThreeTierTestResultDecider<TerminationAnalysisOverallResult> {

	public TerminationAnalysisTestResultDecider(
			final UltimateRunDefinition ultimateRunDefinition, final boolean unknownIsJUnitSuccess) {
		super(ultimateRunDefinition, unknownIsJUnitSuccess);
	}

	@Override
	public IExpectedResultFinder<TerminationAnalysisOverallResult> constructExpectedResultFinder() {
		return new KeywordBasedExpectedResultFinder<>(
				TestUtil.constructFilenameKeywordMap_TerminationAnalysis(),
				TestUtil.constructPathKeywordMap_TerminationAnalysis(),
				TestUtil.constructFirstlineKeywordMap_TerminationAnalysis());
	}

	@Override
	public IOverallResultEvaluator<TerminationAnalysisOverallResult> constructUltimateResultEvaluation() {
		return new TerminationAnalysisOverallResultEvaluator();
	}

	@Override
	public ITestResultEvaluation<TerminationAnalysisOverallResult> constructTestResultEvaluation() {
		return new TerminationAnalysisResultEvaluation();
	}
	
	
	
	public class TerminationAnalysisResultEvaluation implements ITestResultEvaluation<TerminationAnalysisOverallResult> {
		String mCategory;
		String mMessage;
		TestResult mTestResult;

		@Override
		public void evaluateTestResult(
				final IExpectedResultFinder<TerminationAnalysisOverallResult> expectedResultFinder,
				final IOverallResultEvaluator<TerminationAnalysisOverallResult> overallResultDeterminer) {
			evaluateExpectedResult(expectedResultFinder);
			switch (expectedResultFinder.getExpectedResultFinderStatus()) {
			case ERROR:
				// we will not evaluate overall result;
				return;
			case EXPECTED_RESULT_FOUND:
				compareToOverallResult(expectedResultFinder.getExpectedResult(), overallResultDeterminer);
				return;
			case NO_EXPECTED_RESULT_FOUND:
				evaluateOverallResultWithoutExpectedResult(overallResultDeterminer);
				return;
			default:
				throw new IllegalArgumentException();
			}
		}
		
		private void evaluateOverallResultWithoutExpectedResult(
				final IOverallResultEvaluator<TerminationAnalysisOverallResult> overallResultDeterminer) {
			mCategory = overallResultDeterminer.getOverallResult() + "(Expected:UNKNOWN)";
			mMessage += " UltimateResult: " + overallResultDeterminer.generateOverallResultMessage();
			switch (overallResultDeterminer.getOverallResult()) {
			case EXCEPTION_OR_ERROR:
			case UNSUPPORTED_SYNTAX:
			case NO_RESULT:
				mTestResult = TestResult.FAIL;
				break;
			case TERMINATING:
			case NONTERMINATING:
			case UNKNOWN:
			case SYNTAX_ERROR:
			case TIMEOUT:
				mTestResult = TestResult.UNKNOWN;
				break;
			default:
				throw new IllegalArgumentException();
			}
		}

		private void compareToOverallResult(
				final TerminationAnalysisOverallResult expectedResult,
				final IOverallResultEvaluator<TerminationAnalysisOverallResult> overallResultDeterminer) {
			mCategory = overallResultDeterminer.getOverallResult() + "(Expected:" + expectedResult + ")";
			mMessage += " UltimateResult: " + overallResultDeterminer.getOverallResult()
					+ "   " + overallResultDeterminer.generateOverallResultMessage();
				switch (overallResultDeterminer.getOverallResult()) {
				case EXCEPTION_OR_ERROR:
					mTestResult = TestResult.FAIL;
					break;
				case TERMINATING:
					if (expectedResult == TerminationAnalysisOverallResult.TERMINATING) {
						mTestResult = TestResult.SUCCESS;
					} else {
						mTestResult = TestResult.FAIL;
					}
					break;
				case NONTERMINATING:
					if (expectedResult == TerminationAnalysisOverallResult.NONTERMINATING) {
						mTestResult = TestResult.SUCCESS;
					} else {
						mTestResult = TestResult.FAIL;
					}
					break;
				case UNKNOWN:
					// syntax error should always have been found
					if (expectedResult == TerminationAnalysisOverallResult.SYNTAX_ERROR) {
						mTestResult = TestResult.FAIL;
					} else {
						mTestResult = TestResult.UNKNOWN;
					}
					break;
				case SYNTAX_ERROR:
					if (expectedResult == TerminationAnalysisOverallResult.SYNTAX_ERROR) {
						mTestResult = TestResult.SUCCESS;
					} else {
						mTestResult = TestResult.FAIL;
					}
					break;
				case TIMEOUT:
					// syntax error should always have been found
					if (expectedResult == TerminationAnalysisOverallResult.SYNTAX_ERROR) {
						mTestResult = TestResult.FAIL;
					} else {
						mTestResult = TestResult.UNKNOWN;
					}
					break;
				case UNSUPPORTED_SYNTAX:
					mTestResult = TestResult.FAIL;
					break;
				case NO_RESULT:
					mTestResult = TestResult.FAIL;
					break;
				default:
					throw new AssertionError("unknown case");
				}
		}

		private void evaluateExpectedResult(
				final IExpectedResultFinder<TerminationAnalysisOverallResult> expectedResultFinder)
				throws AssertionError {
			switch (expectedResultFinder.getExpectedResultFinderStatus()) {
			case ERROR:
				mCategory = "Inkonsistent keywords";
				mMessage = expectedResultFinder.getExpectedResultFinderMessage();
				mTestResult = TestResult.FAIL;
				break;
			case EXPECTED_RESULT_FOUND:
				mMessage = "ExpectedResult: " + expectedResultFinder.getExpectedResult();
				break;
			case NO_EXPECTED_RESULT_FOUND:
				mMessage = expectedResultFinder.getExpectedResultFinderMessage();
				break;
			default:
				throw new AssertionError("unknown case");
			}
		}

		@Override
		public void evaluateTestResult(
				final IExpectedResultFinder<TerminationAnalysisOverallResult> expectedResultFinder,
				final Throwable e) {
			evaluateExpectedResult(expectedResultFinder);
			switch (expectedResultFinder.getExpectedResultFinderStatus()) {
			case ERROR:
				// we will not evaluate overall result;
				return;
			case EXPECTED_RESULT_FOUND:
			case NO_EXPECTED_RESULT_FOUND:
				mCategory += "/UltimateResult:" + TerminationAnalysisOverallResult.EXCEPTION_OR_ERROR;
				mMessage += " UltimateResult: " + e.getMessage();
				break;
			default:
				break;
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
