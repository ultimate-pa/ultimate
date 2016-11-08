/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.lib.results.AutomataScriptInterpreterOverallResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AutomataScriptInterpreterOverallResult.OverallResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

public class AutomataScriptTestResultDecider implements ITestResultDecider {

	private OverallResult mCategory;
	private String mErrorMessage;

	@Override
	public TestResult getTestResult(final IUltimateServiceProvider  services) {
		AutomataScriptInterpreterOverallResult asior = null;
		final Map<String, List<IResult>> allResults = services.getResultService().getResults();
		for (final Entry<String, List<IResult>> entry : allResults.entrySet()) {
			for (final IResult iResult : entry.getValue()) {
				if (iResult instanceof AutomataScriptInterpreterOverallResult) {
					asior = (AutomataScriptInterpreterOverallResult) iResult;
				}
			}
		}
		if (asior == null) {
			throw new AssertionError("no overall result - interpretation of ats file failed");
		} else {
			mCategory = asior.getOverallResult();
			if (mCategory == OverallResult.EXCEPTION_OR_ERROR || mCategory == OverallResult.TIMEOUT) {
				mErrorMessage = asior.getErrorMessage();
			} else {
				mErrorMessage = null;
			}
		}
		return getTestResultFromCategory(mCategory);
	}

	@Override
	public TestResult getTestResult(final IUltimateServiceProvider service, final Throwable e) {
		mCategory = OverallResult.EXCEPTION_OR_ERROR;
		return getTestResultFromCategory(mCategory);
	}

	@Override
	public String getResultMessage() {
		if (mCategory == OverallResult.EXCEPTION_OR_ERROR || mCategory == OverallResult.TIMEOUT) {
			return mCategory.toString() + " " + mErrorMessage;
		} else {
			return mCategory.toString();
		}
	}

	@Override
	public String getResultCategory() {
		return mCategory.toString();
	}

	@Override
	public boolean getJUnitSuccess(final TestResult actualResult) {
		switch (actualResult) {
		case SUCCESS:
		case UNKNOWN:
			return true;
		case FAIL:
			return false;
		default:
			throw new AssertionError();
		}
	}

	private TestResult getTestResultFromCategory(final OverallResult category) {
		switch (category) {
		case ALL_ASSERTIONS_HOLD:
		case NO_ASSERTION:
			return TestResult.SUCCESS;
		case EXCEPTION_OR_ERROR:
		case SOME_ASSERTION_FAILED:
			return TestResult.FAIL;
		case TIMEOUT:
			return TestResult.UNKNOWN;
		case OUT_OF_MEMORY:
			return TestResult.UNKNOWN;
		default:
			throw new AssertionError();
		}
	}

}
