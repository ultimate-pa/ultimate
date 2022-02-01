/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.test.decider.expectedresult;

import java.io.File;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;

/**
 * Looks for a line of the form "(set-info :status ..)" and returns the according expected result
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <OVERALL_RESULT>
 */
public class SMTLibExpectedResultFinder<OVERALL_RESULT> extends AbstractExpectedResultFinder<OVERALL_RESULT> {
	
	private final OVERALL_RESULT mUnknownResult;
	private final OVERALL_RESULT mSatResult;
	private final OVERALL_RESULT mUnsatResult;
	
	public SMTLibExpectedResultFinder(OVERALL_RESULT unknownResult, OVERALL_RESULT satResult, 
			OVERALL_RESULT unsatResult) {
		mUnknownResult = unknownResult;
		mSatResult = satResult;
		mUnsatResult = unsatResult;
	}

	@Override
	public void findExpectedResult(UltimateRunDefinition ultimateRunDefinition) {
		final File file = ultimateRunDefinition.selectPrimaryInputFile();
		if (file == null) {
			mEvaluationStatus = ExpectedResultFinderStatus.NO_EXPECTED_RESULT_FOUND;
			mExpectedResultEvaluation = "Could not determine expected result; ulitmateRunDefinition of test case "
					+ "contained no file";
			mExpectedResult = mUnknownResult;
			return;
		}

		final String statusInfoLine = TestUtil.extractSMTLibStatusInfo(file);
		if (statusInfoLine == null) {
			mEvaluationStatus = ExpectedResultFinderStatus.NO_EXPECTED_RESULT_FOUND;
			mExpectedResultEvaluation = "Could not determine expected result; found no line of the form "
					+ "(set-info :status ...) in the input file.";
			mExpectedResult = mUnknownResult;
			return;
		}

		if (statusInfoLine.contains("unknown")) {
			mExpectedResult = mUnknownResult;
		}
		if (statusInfoLine.contains("unsat")) {
			mExpectedResult = mUnsatResult;
		} else if (statusInfoLine.contains("sat")) {
			mExpectedResult = mSatResult;
		}
		mEvaluationStatus = ExpectedResultFinderStatus.EXPECTED_RESULT_FOUND;
		mExpectedResultEvaluation = "Expected result: " + mExpectedResult;
	}
}
