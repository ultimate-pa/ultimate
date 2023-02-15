/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.decider.expectedresult.IExpectedResultFinder;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.IOverallResultEvaluator;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;

/**
 * Abstract class for deciding a test result in three steps:
 * <ul>
 * <li>1. Use IExpectedResultFinder to decide expected result for an UltimateRunDefinition
 * <li>2. Use IResults from Ultimate to decide the overall result provided by Ultimate
 * <li>3. Compare expected result with the overall result computed by ultimate to decide the test result.
 * </ul>
 *
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <OVERALL_RESULT>
 */
public abstract class ThreeTierTestResultDecider<OVERALL_RESULT> implements ITestResultDecider {

	/**
	 * if true the TestResult UNKNOWN is a success for JUnit, if false, the TestResult UNKNOWN is a failure for JUnit.
	 */
	private final boolean mUnknownIsJUnitSuccess;
	private final UltimateRunDefinition mUltimateRunDefinition;
	private final IExpectedResultFinder<OVERALL_RESULT> mExpectedResultEvaluation;
	private IOverallResultEvaluator<OVERALL_RESULT> mUltimateResultEvaluation;
	private ITestResultEvaluation<OVERALL_RESULT> mTestResultEvaluation;
	protected final String mOverridenExpectedVerdict;

	/**
	 *
	 * @param ultimateRunDefinition
	 *
	 * @param unknownIsJUnitSuccess
	 *            if true the TestResult UNKNOWN is a success for JUnit, if false, the TestResult UNKNOWN is a failure
	 *            for JUnit.
	 *
	 * @param isIgnored
	 *            Is the test case ignored?
	 */
	public ThreeTierTestResultDecider(final UltimateRunDefinition ultimateRunDefinition,
			final boolean unknownIsJUnitSuccess, final String overridenExpectedVerdict) {
		mUnknownIsJUnitSuccess = unknownIsJUnitSuccess;
		mOverridenExpectedVerdict = overridenExpectedVerdict;
		mUltimateRunDefinition = ultimateRunDefinition;
		mExpectedResultEvaluation = constructExpectedResultFinder();
		mExpectedResultEvaluation.findExpectedResult(ultimateRunDefinition);
	}

	/**
	 *
	 * @param ultimateRunDefinition
	 *
	 * @param unknownIsJUnitSuccess
	 *            if true the TestResult UNKNOWN is a success for JUnit, if false, the TestResult UNKNOWN is a failure
	 *            for JUnit.
	 */
	public ThreeTierTestResultDecider(final UltimateRunDefinition ultimateRunDefinition,
			final boolean unknownIsJUnitSuccess) {
		this(ultimateRunDefinition, unknownIsJUnitSuccess, null);
	}

	@Override
	public final TestResult getTestResult(final IUltimateServiceProvider services) {
		mUltimateResultEvaluation = constructUltimateResultEvaluation();
		mUltimateResultEvaluation.evaluateOverallResult(services.getResultService());
		mTestResultEvaluation = constructTestResultEvaluation();
		mTestResultEvaluation.evaluateTestResult(mExpectedResultEvaluation, mUltimateResultEvaluation);
		writeResultLogMessages(services);
		return mTestResultEvaluation.getTestResult();
	}

	@Override
	public final TestResult getTestResult(final IUltimateServiceProvider services, final Throwable e) {
		mTestResultEvaluation = constructTestResultEvaluation();
		mTestResultEvaluation.evaluateTestResult(mExpectedResultEvaluation, e);
		writeResultLogMessages(services);
		return mTestResultEvaluation.getTestResult();
	}

	private final void writeResultLogMessages(final IUltimateServiceProvider services) {
		final List<String> messages = new ArrayList<>();
		messages.add("Expected: " + mExpectedResultEvaluation.getExpectedResultFinderMessage());
		messages.add("Actual: " + mUltimateResultEvaluation.generateOverallResultMessage());
		messages.add("Test result: " + mTestResultEvaluation.getTestResult().toString());

		TestUtil.logResults(getClass(), mUltimateRunDefinition.toString(),
				!getJUnitSuccess(mTestResultEvaluation.getTestResult()), messages, services);
	}

	@Override
	public final String getResultMessage() {
		return mTestResultEvaluation.getTestResultMessage();
	}

	@Override
	public final String getResultCategory() {
		return mTestResultEvaluation.getTestResultCategory();
	}

	@Override
	public boolean getJUnitSuccess(final TestResult testResult) {
		switch (testResult) {
		case SUCCESS:
			return true;
		case UNKNOWN:
			return mUnknownIsJUnitSuccess;
		case FAIL:
			return false;
		case IGNORE:
			return false;
		default:
			throw new AssertionError("unknown actualResult: " + testResult);
		}

	}

	public abstract IExpectedResultFinder<OVERALL_RESULT> constructExpectedResultFinder();

	public abstract IOverallResultEvaluator<OVERALL_RESULT> constructUltimateResultEvaluation();

	public abstract ITestResultEvaluation<OVERALL_RESULT> constructTestResultEvaluation();

	public interface ITestResultEvaluation<OVERALL_RESULT> {
		public void evaluateTestResult(IExpectedResultFinder<OVERALL_RESULT> expectedResultEvaluation,
				IOverallResultEvaluator<OVERALL_RESULT> overallResultDeterminer);

		public void evaluateTestResult(IExpectedResultFinder<OVERALL_RESULT> expectedResultEvaluation, Throwable e);

		public TestResult getTestResult();

		public String getTestResultCategory();

		public String getTestResultMessage();
	}
}
