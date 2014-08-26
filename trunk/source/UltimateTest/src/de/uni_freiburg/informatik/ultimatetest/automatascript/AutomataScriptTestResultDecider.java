package de.uni_freiburg.informatik.ultimatetest.automatascript;

import java.util.HashMap;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimate.result.AutomataScriptInterpreterOverallResult;
import de.uni_freiburg.informatik.ultimate.result.AutomataScriptInterpreterOverallResult.OverallResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;

public class AutomataScriptTestResultDecider implements ITestResultDecider {
	
	OverallResult m_Category;

	@Override
	public TestResult getTestResult(IResultService resultService) {
		AutomataScriptInterpreterOverallResult asior = null;
		HashMap<String, List<IResult>> allResults = resultService.getResults();
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
		return m_Category.toString();
	}

	@Override
	public String getResultCategory() {
		return m_Category.toString();
	}

	@Override
	public boolean getJUnitTestResult(TestResult actualResult) {
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
		default:
			throw new AssertionError();
		}
	}

}
