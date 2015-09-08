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
package de.uni_freiburg.informatik.ultimatetest.decider;

import java.util.ArrayList;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.decider.expectedResult.IExpectedResultFinder;
import de.uni_freiburg.informatik.ultimatetest.decider.overallResult.IOverallResultEvaluator;
import de.uni_freiburg.informatik.ultimatetest.util.TestUtil;

/**
 * Abstract class for deciding a test result in three steps:
 * <ul>
 * <li>1. Use IExpectedResultFinder to decide expected result for an
 * UltimateRunDefinition
 * <li>2. Use IResults from Ultimate to decide the overall result provided by
 * Ultimate
 * <li>3. Compare expected result with the overall result computed by ultimate
 * to decide the test result.
 * </ul>
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 * @param <OVERALL_RESULT>
 */
public abstract class ThreeTierTestResultDecider<OVERALL_RESULT> implements ITestResultDecider {

	/**
	 * if true the TestResult UNKNOWN is a success for JUnit, if false, the
	 * TestResult UNKNOWN is a failure for JUnit.
	 */
	private final boolean m_UnknownIsJUnitSuccess;
	private final UltimateRunDefinition m_UltimateRunDefinition;
	private final IExpectedResultFinder<OVERALL_RESULT> m_ExpectedResultEvaluation;
	private IOverallResultEvaluator<OVERALL_RESULT> m_UltimateResultEvaluation;
	private ITestResultEvaluation<OVERALL_RESULT> m_TestResultEvaluation;

	/**
	 * 
	 * @param ultimateRunDefinition
	 * 
	 * @param unknownIsJUnitSuccess
	 *            if true the TestResult UNKNOWN is a success for JUnit, if
	 *            false, the TestResult UNKNOWN is a failure for JUnit.
	 */
	public ThreeTierTestResultDecider(UltimateRunDefinition ultimateRunDefinition, boolean unknownIsJUnitSuccess) {
		m_UnknownIsJUnitSuccess = unknownIsJUnitSuccess;
		m_UltimateRunDefinition = ultimateRunDefinition;
		m_ExpectedResultEvaluation = constructExpectedResultFinder();
		m_ExpectedResultEvaluation.findExpectedResult(ultimateRunDefinition);
	}

	@Override
	public final TestResult getTestResult(IResultService resultService) {
		m_UltimateResultEvaluation = constructUltimateResultEvaluation();
		m_UltimateResultEvaluation.evaluateOverallResult(resultService);
		m_TestResultEvaluation = constructTestResultEvaluation();
		m_TestResultEvaluation.evaluateTestResult(m_ExpectedResultEvaluation, m_UltimateResultEvaluation);
		writeResultLogMessages(resultService);
		return m_TestResultEvaluation.getTestResult();
	}

	@Override
	public final TestResult getTestResult(IResultService resultService, Throwable e) {
		m_TestResultEvaluation = constructTestResultEvaluation();
		m_TestResultEvaluation.evaluateTestResult(m_ExpectedResultEvaluation, e);
		writeResultLogMessages(resultService);
		return m_TestResultEvaluation.getTestResult();
	}

	private final void writeResultLogMessages(IResultService resultService) {
		Logger log = Logger.getLogger(getClass());
		ArrayList<String> messages = new ArrayList<>();
		messages.add("Expected: " + m_ExpectedResultEvaluation.getExpectedResultFinderMessage());
		messages.add("Actual: " + m_UltimateResultEvaluation.generateOverallResultMessage());
		messages.add("Test result: "+m_TestResultEvaluation.getTestResult().toString());

		TestUtil.logResults(log, m_UltimateRunDefinition.generateShortStringRepresentation(),
				!getJUnitSuccess(m_TestResultEvaluation.getTestResult()), messages, resultService);
	}

	@Override
	public final String getResultMessage() {
		return m_TestResultEvaluation.getTestResultMessage();
	}

	@Override
	public final String getResultCategory() {
		return m_TestResultEvaluation.getTestResultCategory();
	}

	@Override
	public boolean getJUnitSuccess(TestResult testResult) {
		switch (testResult) {
		case SUCCESS:
			return true;
		case UNKNOWN:
			return m_UnknownIsJUnitSuccess;
		case FAIL:
			return false;
		default:
			throw new AssertionError("unknown actualResult");
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
