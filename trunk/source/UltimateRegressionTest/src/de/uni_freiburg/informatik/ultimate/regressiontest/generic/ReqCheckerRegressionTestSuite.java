/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultUtil;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.pea2boogie.results.ReqCheck;
import de.uni_freiburg.informatik.ultimate.pea2boogie.results.ReqCheckFailResult;
import de.uni_freiburg.informatik.ultimate.pea2boogie.results.ReqCheckSuccessResult;
import de.uni_freiburg.informatik.ultimate.pea2boogie.results.RequirementInconsistentErrorResult;
import de.uni_freiburg.informatik.ultimate.regressiontest.AbstractRegressionTestSuite;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimate.test.decider.ThreeTierTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.ThreeTierTestResultDecider.ITestResultEvaluation;
import de.uni_freiburg.informatik.ultimate.test.decider.expectedresult.IExpectedResultFinder;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.IOverallResultEvaluator;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * Regression tests for Requirements Checker.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ReqCheckerRegressionTestSuite extends AbstractRegressionTestSuite {

	private static final int TIMEOUT = 10_000;

	public ReqCheckerRegressionTestSuite() {
		super();
		mTimeout = TIMEOUT;
		mRootFolder = TestUtil.getPathFromTrunk("examples/Requirements");
		mFiletypesToConsider = new String[] { ".req" };
	}

	@Override
	protected ITestResultDecider getTestResultDecider(final UltimateRunDefinition runDefinition) {
		return new ReqCheckerTestResultDecider(runDefinition, false);
	}

	private static final class ReqCheckerResult {

		private final Set<Set<String>> mRtInconsistent;
		private final Set<String> mVacuous;
		private final Set<String> mInconsistent;
		private final int mNoResults;
		private final boolean mIsIrregular;

		private String mOverallResultMessage;

		public ReqCheckerResult(final Set<Set<String>> rtInconsistent, final Set<String> vacuous,
				final Set<String> inconsistent, final int results) {
			mRtInconsistent = Objects.requireNonNull(rtInconsistent);
			mVacuous = Objects.requireNonNull(vacuous);
			mInconsistent = Objects.requireNonNull(inconsistent);
			if (results < 0) {
				throw new IllegalArgumentException("negative number of results");
			}
			mNoResults = results;
			mIsIrregular = false;
			mOverallResultMessage = createString();
		}

		public ReqCheckerResult() {
			this(Collections.emptySet(), Collections.emptySet(), Collections.emptySet(), 0);
		}

		public ReqCheckerResult(final Collection<IResult> flatResults) {
			final Set<Set<String>> rtInconsistent = new HashSet<>();
			final Set<String> vacuous = new HashSet<>();
			final Set<String> inconsistent = new HashSet<>();

			int results = 0;
			for (final IResult result : flatResults) {
				if (result instanceof RequirementInconsistentErrorResult) {
					final Set<String> ids = ((RequirementInconsistentErrorResult) result).getIds();
					inconsistent.addAll(ids);
					results++;
				} else if (result instanceof ReqCheckSuccessResult) {
					results++;
				} else if (result instanceof ReqCheckFailResult) {
					final ReqCheck check = ((ReqCheckFailResult<?>) result).getCheck();
					final Set<String> ids = check.getIds();
					assert check.getSpec().size() == 1;
					final Spec spec = check.getSpec().iterator().next();
					switch (spec) {
					case RTINCONSISTENT:
						rtInconsistent.add(ids);
						break;
					case VACUOUS:
						vacuous.addAll(ids);
						break;
					case CONSISTENCY:
						inconsistent.addAll(ids);
						break;
					default:
						throw new UnsupportedOperationException("Unsupported spec: " + spec);
					}
					results++;
				} else if (result instanceof ExceptionOrErrorResult || result instanceof TimeoutResult) {
					mIsIrregular = true;
					mNoResults = 0;
					mVacuous = Collections.emptySet();
					mRtInconsistent = Collections.emptySet();
					mInconsistent = Collections.emptySet();
					mOverallResultMessage = result.getLongDescription();
					return;
				}
			}

			mIsIrregular = false;
			mNoResults = results;
			mVacuous = vacuous;
			mRtInconsistent = rtInconsistent;
			mInconsistent = inconsistent;
			mOverallResultMessage = createString();

		}

		public ReqCheckerResult merge(final ReqCheckerResult expectedResultForFile) {
			final Set<Set<String>> newRtInconsistent =
					DataStructureUtils.union(mRtInconsistent, expectedResultForFile.mRtInconsistent);
			final Set<String> newVacuous = DataStructureUtils.union(mVacuous, expectedResultForFile.mVacuous);
			final Set<String> newInconsistent =
					DataStructureUtils.union(mInconsistent, expectedResultForFile.mInconsistent);
			final int newNoResults = mNoResults + expectedResultForFile.mNoResults;
			return new ReqCheckerResult(newRtInconsistent, newVacuous, newInconsistent, newNoResults);
		}

		public String generateOverallResultMessage() {
			return mOverallResultMessage;
		}

		private String createString() {
			final StringBuilder sb = new StringBuilder();
			sb.append("rt-inconsistent:");
			for (final Set<String> inc : mRtInconsistent) {
				for (final String sinc : inc) {
					sb.append(sinc).append('+');
				}
				sb.append(',');
			}
			sb.append(';');
			sb.append("vacuous:");
			for (final String vac : mVacuous) {
				sb.append(vac).append(',');
			}
			sb.append(';');
			sb.append("inconsistent:");
			for (final String inc : mInconsistent) {
				sb.append(inc).append(',');
			}
			sb.append(';');
			sb.append("results:").append(mNoResults);
			return sb.toString();
		}

		public boolean isSuccess(final ReqCheckerResult actual) {
			if (actual.mIsIrregular) {
				return false;
			}
			if (actual.mNoResults != mNoResults) {
				return false;
			}
			if (DataStructureUtils.isDifferent(actual.mInconsistent, mInconsistent)) {
				return false;
			}
			if (DataStructureUtils.isDifferent(actual.mVacuous, mVacuous)) {
				return false;
			}
			if (DataStructureUtils.isDifferent(actual.mRtInconsistent, mRtInconsistent)) {
				return false;
			}
			return true;
		}

		public String generateDeltaMessage(final ReqCheckerResult actual) {
			if (actual.mIsIrregular) {
				return actual.mOverallResultMessage;
			}
			final String msg = "%s different. Expected: %s. Actual %s.";
			if (actual.mNoResults != mNoResults) {
				return String.format(msg, "Number of results", mNoResults, actual.mNoResults);
			}
			if (DataStructureUtils.isDifferent(actual.mInconsistent, mInconsistent)) {
				return String.format(msg, "Inconsistent requirements", mInconsistent, actual.mInconsistent);
			}
			if (DataStructureUtils.isDifferent(actual.mVacuous, mVacuous)) {
				return String.format(msg, "Vacuous requirements", mVacuous, actual.mVacuous);
			}
			if (DataStructureUtils.isDifferent(actual.mRtInconsistent, mRtInconsistent)) {
				return String.format(msg, "Rt-inconsistent requirements", mRtInconsistent, actual.mRtInconsistent);
			}
			return "As expected";
		}
	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	private static final class ReqCheckerTestResultDecider extends ThreeTierTestResultDecider<ReqCheckerResult> {

		public ReqCheckerTestResultDecider(final UltimateRunDefinition ultimateRunDefinition,
				final boolean unknownIsJUnitSuccess) {
			super(ultimateRunDefinition, unknownIsJUnitSuccess);
		}

		@Override
		public IExpectedResultFinder<ReqCheckerResult> constructExpectedResultFinder() {
			return new ReqCheckerExpectedResultFinder();
		}

		@Override
		public IOverallResultEvaluator<ReqCheckerResult> constructUltimateResultEvaluation() {
			return new ReqCheckerResultEvaluator();
		}

		@Override
		public ITestResultEvaluation<ReqCheckerResult> constructTestResultEvaluation() {
			return new ReqCheckerTestResultEvaluation();
		}

	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	private static final class ReqCheckerResultEvaluator implements IOverallResultEvaluator<ReqCheckerResult> {

		private ReqCheckerResult mResult;

		@Override
		public void evaluateOverallResult(final IResultService resultService) {
			final Collection<IResult> flatResults = ResultUtil.filterResults(resultService.getResults(), a -> true);
			mResult = new ReqCheckerResult(flatResults);
		}

		@Override
		public ReqCheckerResult getOverallResult() {
			return mResult;
		}

		@Override
		public String generateOverallResultMessage() {
			return mResult.generateOverallResultMessage();
		}

		@Override
		public Set<IResult> getMostSignificantResults() {
			return Collections.emptySet();
		}
	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	private static final class ReqCheckerExpectedResultFinder implements IExpectedResultFinder<ReqCheckerResult> {

		private enum Error {
			CANNOT_READ, NO_SPEC, BROKEN_SPEC
		}

		private static final String KEYWORD = "#TestSpec:";

		private ExpectedResultFinderStatus mFinderStatus;
		private String mErrorMessage;
		private ReqCheckerResult mResult;

		private ReqCheckerExpectedResultFinder() {
			mFinderStatus = ExpectedResultFinderStatus.ERROR;
			mErrorMessage = getClass().getSimpleName() + " has not seen any result";
			mResult = null;
		}

		@Override
		public void findExpectedResult(final UltimateRunDefinition urd) {
			final Map<String, Error> errors = new HashMap<>();
			ReqCheckerResult expectedResult = new ReqCheckerResult();
			for (final File file : urd.getInput()) {
				if (!file.canRead()) {
					errors.put(file.getAbsolutePath(), Error.CANNOT_READ);
					continue;
				}
				final String firstLine = TestUtil.extractFirstLine(file);
				final int idx = firstLine.indexOf(KEYWORD);
				if (idx == -1) {
					errors.put(file.getAbsolutePath(), Error.NO_SPEC);
					continue;
				}
				final ReqCheckerResult expectedResultForFile =
						createExpectedResult(firstLine.substring(idx + KEYWORD.length()));
				if (expectedResultForFile == null) {
					errors.put(file.getAbsolutePath(), Error.BROKEN_SPEC);
					continue;
				}
				expectedResult = expectedResult.merge(expectedResultForFile);
			}
			if (errors.isEmpty()) {
				mResult = expectedResult;
				mFinderStatus = ExpectedResultFinderStatus.EXPECTED_RESULT_FOUND;
			} else {
				mResult = null;
				mErrorMessage = errors.toString();
				if (expectedResult == null) {
					mFinderStatus = ExpectedResultFinderStatus.NO_EXPECTED_RESULT_FOUND;
				} else {
					mFinderStatus = ExpectedResultFinderStatus.ERROR;
				}
			}
		}

		private static ReqCheckerResult createExpectedResult(final String substring) {
			final String[] splitted = substring.split(";");
			final Set<Set<String>> rtInconsistent = new HashSet<>();
			final Set<String> vacuous = new HashSet<>();
			final Set<String> inconsistent = new HashSet<>();
			int results = -1;
			final Function<String, String> trim = ReqCheckerExpectedResultFinder::trim;
			for (final String entry : splitted) {
				final String[] kwp = entry.split(":");
				if (kwp.length < 1) {
					return null;
				}
				final String keyword = trim.apply(kwp[0]);
				final String value;
				if (kwp.length == 2) {
					value = trim.apply(kwp[1]);
				} else {
					value = "";
					if (kwp.length > 2) {
						return null;
					}
				}

				switch (keyword) {
				case "rt-inconsistent":
					final String[] subsets = value.split(",");
					for (final String subset : subsets) {
						final Set<String> subsetSet = Arrays.stream(subset.split("\\+")).map(trim)
								.filter(a -> !a.isEmpty()).collect(Collectors.toSet());
						if (!subset.isEmpty()) {
							rtInconsistent.add(subsetSet);
						}
					}
					break;
				case "vacuous":
					Arrays.stream(value.split(",")).map(trim).filter(a -> !a.isEmpty()).forEach(vacuous::add);
					break;
				case "inconsistent":
					Arrays.stream(value.split(",")).map(trim).filter(a -> !a.isEmpty()).forEach(inconsistent::add);
					break;
				case "results":
					if (results != -1) {
						return null;
					}
					results = Integer.parseInt(value);
					break;
				default:
					return null;
				}
			}
			return new ReqCheckerResult(rtInconsistent, vacuous, inconsistent, results);
		}

		private static String trim(final String s) {
			return s.replaceAll("\\s", "");
		}

		@Override
		public ExpectedResultFinderStatus getExpectedResultFinderStatus() {
			return mFinderStatus;
		}

		@Override
		public String getExpectedResultFinderMessage() {
			switch (mFinderStatus) {
			case ERROR:
				return mErrorMessage;
			case EXPECTED_RESULT_FOUND:
				return mResult.generateOverallResultMessage();
			case NO_EXPECTED_RESULT_FOUND:
				return "No expected result";
			default:
				throw new UnsupportedOperationException("Unknown finder status: " + mFinderStatus);
			}
		}

		@Override
		public ReqCheckerResult getExpectedResult() {
			return mResult;
		}

	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	private static final class ReqCheckerTestResultEvaluation implements ITestResultEvaluation<ReqCheckerResult> {

		private TestResult mTestResult;
		private String mCategory;
		private String mMessage;

		@Override
		public void evaluateTestResult(final IExpectedResultFinder<ReqCheckerResult> expectedResultEvaluation,
				final IOverallResultEvaluator<ReqCheckerResult> overallResultDeterminer) {
			final ReqCheckerResult expected = expectedResultEvaluation.getExpectedResult();
			final ReqCheckerResult actual = overallResultDeterminer.getOverallResult();

			if (expected == null) {
				mTestResult = TestResult.UNKNOWN;
				mCategory = "MISSING SPEC";
				mMessage = "Did not find test specification";
			} else if (expected.isSuccess(actual)) {
				mTestResult = TestResult.SUCCESS;
				mCategory = "SUCCESS";
				mMessage = expected.generateOverallResultMessage();
			} else {
				mTestResult = TestResult.FAIL;
				mCategory = "FAIL";
				mMessage = expected.generateDeltaMessage(actual);
			}
		}

		@Override
		public void evaluateTestResult(final IExpectedResultFinder<ReqCheckerResult> expectedResultEvaluation,
				final Throwable e) {
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
