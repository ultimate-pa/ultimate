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
package de.uni_freiburg.informatik.ultimatetest.decider;

import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.services.model.IResultService;
import de.uni_freiburg.informatik.ultimate.result.AutomataScriptInterpreterOverallResult;
import de.uni_freiburg.informatik.ultimate.result.AutomataScriptInterpreterOverallResult.OverallResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;

public class AutomataScriptTestResultDecider implements ITestResultDecider {
	
	private OverallResult m_Category;
	private String m_ErrorMessage;

	@Override
	public TestResult getTestResult(IResultService resultService) {
		AutomataScriptInterpreterOverallResult asior = null;
		Map<String, List<IResult>> allResults = resultService.getResults();
		for (Entry<String, List<IResult>> entry  : allResults.entrySet()) {
			for (IResult iResult : entry.getValue()) {
				if (iResult instanceof AutomataScriptInterpreterOverallResult) {
					asior = (AutomataScriptInterpreterOverallResult) iResult;
				}
			}
		}
		if (asior == null) {
			throw new AssertionError("no overall result");
		} else {
			m_Category = asior.getOverallResult();
			if(m_Category == OverallResult.EXCEPTION_OR_ERROR) {
				m_ErrorMessage = asior.getErrorMessage();
			} else {
				m_ErrorMessage = null;
			}
		}
		return getTestResultFromCategory(m_Category);
	}

	@Override
	public TestResult getTestResult(IResultService resultService,
			Throwable e) {
		m_Category = OverallResult.EXCEPTION_OR_ERROR;
		return getTestResultFromCategory(m_Category);
	}

	@Override
	public String getResultMessage() {
		if (m_Category == OverallResult.EXCEPTION_OR_ERROR) {
			return m_Category.toString() + " " + m_ErrorMessage;
		} else {
			return m_Category.toString();
		}
	}

	@Override
	public String getResultCategory() {
		return m_Category.toString();
	}

	@Override
	public boolean getJUnitSuccess(TestResult actualResult) {
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
	
	private TestResult getTestResultFromCategory(OverallResult category) {
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
