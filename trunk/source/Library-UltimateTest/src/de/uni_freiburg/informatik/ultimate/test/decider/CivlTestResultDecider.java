/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 École Polytechnique
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

import java.util.Set;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.civlizer.results.CivlFailureResult;
import de.uni_freiburg.informatik.ultimate.civlizer.results.CivlSuccessResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TypeErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnsupportedSyntaxResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.ITimeoutResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.decider.expectedresult.IExpectedResultFinder;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.IOverallResultEvaluator;

public class CivlTestResultDecider extends ThreeTierTestResultDecider<CivlTestResultDecider.CivlOverallResult> {
	private static final String CIVLIZER_PLUGIN_ID = "de.uni_freiburg.informatik.ultimate.civlizer";

	public enum CivlOverallResult {
		VERIFIED, CIVL_ERRORS, CRASH, SYNTAX_ERROR, TIMEOUT
	}

	public CivlTestResultDecider(final UltimateRunDefinition urd) {
		super(urd, false);
	}

	@Override
	public IExpectedResultFinder<CivlOverallResult> constructExpectedResultFinder() {
		return new ExpectedResultFinder();
	}

	@Override
	public IOverallResultEvaluator<CivlOverallResult> constructUltimateResultEvaluation() {
		return new OverallResultEvaluator();
	}

	@Override
	public ITestResultEvaluation<CivlOverallResult> constructTestResultEvaluation() {
		return new TestResultEvaluation();
	}

	private static final class ExpectedResultFinder implements IExpectedResultFinder<CivlOverallResult> {
		@Override
		public void findExpectedResult(final UltimateRunDefinition ultimateRunDefinition) {
			// for now, nothing to be done here
		}

		@Override
		public ExpectedResultFinderStatus getExpectedResultFinderStatus() {
			return ExpectedResultFinderStatus.EXPECTED_RESULT_FOUND;
		}

		@Override
		public String getExpectedResultFinderMessage() {
			return "CivlExpectedResultFinder always expects success";
		}

		@Override
		public CivlOverallResult getExpectedResult() {
			return CivlOverallResult.VERIFIED;
		}
	}

	private static final class OverallResultEvaluator implements IOverallResultEvaluator<CivlOverallResult> {
		private CivlOverallResult mOverallResult;
		private String mOverallMessage;
		private IResult mMostSignificantResult;

		@Override
		public void evaluateOverallResult(final IResultService resultService) {
			for (final var entry : resultService.getResults().entrySet()) {
				for (final var result : entry.getValue()) {
					if (result instanceof final ExceptionOrErrorResult e) {
						mOverallResult = CivlOverallResult.CRASH;
						mOverallMessage = e.getLongDescription();
						mMostSignificantResult = e;
						return;
					}
					if (result instanceof TypeErrorResult || result instanceof SyntaxErrorResult
							|| result instanceof UnsupportedSyntaxResult) {
						mOverallResult = CivlOverallResult.SYNTAX_ERROR;
						mOverallMessage = result.getLongDescription();
						mMostSignificantResult = result;
						return;
					}
					if (result instanceof ITimeoutResult) {
						mOverallResult = CivlOverallResult.TIMEOUT;
						mOverallMessage = result.getLongDescription();
						mMostSignificantResult = result;
						return;
					}
				}
			}

			final var results = resultService.getResults().get(CIVLIZER_PLUGIN_ID);
			if (results == null || results.isEmpty()) {
				throw new IllegalStateException("No Civlizer results found. Did you configure Civlizer to run Civl?");
			}

			for (final var result : results) {
				if (result instanceof final CivlSuccessResult s) {
					mOverallResult = CivlOverallResult.VERIFIED;
					mOverallMessage = s.getLongDescription();
					mMostSignificantResult = s;
					break;
				}
				if (result instanceof final CivlFailureResult f) {
					mOverallResult = CivlOverallResult.CIVL_ERRORS;
					mOverallMessage = f.getLongDescription();
					mMostSignificantResult = f;
					break;
				}
			}
		}

		@Override
		public CivlOverallResult getOverallResult() {
			return mOverallResult;
		}

		@Override
		public String generateOverallResultMessage() {
			return mOverallMessage;
		}

		@Override
		public Set<IResult> getMostSignificantResults() {
			return Set.of(mMostSignificantResult);
		}
	}

	public class TestResultEvaluation implements ITestResultEvaluation<CivlOverallResult> {
		private TestResult mTestResult;
		private String mCategory;
		private String mMessage;

		@Override
		public void evaluateTestResult(final IExpectedResultFinder<CivlOverallResult> expectedResultEvaluation,
				final IOverallResultEvaluator<CivlOverallResult> overallResultDeterminer) {
			final CivlOverallResult expectedResult = expectedResultEvaluation.getExpectedResult();
			final CivlOverallResult actualResult = overallResultDeterminer.getOverallResult();
			final String overallResultMsg = overallResultDeterminer.generateOverallResultMessage();

			if (mOverridenExpectedVerdict != null) {
				final Pattern pattern = Pattern.compile(mOverridenExpectedVerdict, Pattern.CASE_INSENSITIVE);
				if (pattern.matcher(actualResult.toString()) != null || pattern.matcher(overallResultMsg) != null) {
					mTestResult = TestResult.IGNORE;
				} else {
					mTestResult = TestResult.FAIL;
				}
				mCategory = actualResult + " (Expected to match :" + mOverridenExpectedVerdict + ")";
				mMessage = " UltimateResult: " + overallResultMsg;
				return;
			}

			if (expectedResult == actualResult) {
				mCategory = "precise match of results (and results are not both UNKOWN).";
				mMessage = "both results are " + expectedResult;
				mTestResult = TestResult.SUCCESS;
				return;
			}

			mCategory = "results don't match";
			mMessage = "expected: " + expectedResult + " actual: " + actualResult + "   " + overallResultMsg;
			mTestResult = TestResult.FAIL;
		}

		@Override
		public void evaluateTestResult(final IExpectedResultFinder<CivlOverallResult> expectedResultEvaluation,
				final Throwable e) {
			final CivlOverallResult expectedResult = expectedResultEvaluation.getExpectedResult();

			mCategory = "threw an exception";
			mMessage = "expected: " + expectedResult + " actual: threw an exception";
			mTestResult = TestResult.FAIL;
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
