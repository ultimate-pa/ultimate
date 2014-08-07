package de.uni_freiburg.informatik.ultimatetest.automatascript;

import java.util.HashMap;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.IResultWithSeverity;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;

public class AutomataScriptTestResultDecider implements ITestResultDecider {
	
	enum AutomataScriptTestResultCategory {
		ALL_HOLD, ALL_HOLD_TRIVIALLY, SOME_FAIL, EXCEPTION_OR_ERROR, TIMEOUT, SYNTAX_ERROR
	}

	AutomataScriptTestResultCategory m_Category = AutomataScriptTestResultCategory.ALL_HOLD_TRIVIALLY;

	@Override
	public TestResult getTestResult(IUltimateServiceProvider services) {
		HashMap<String, List<IResult>> allResults = services.getResultService().getResults();
		for (Entry<String, List<IResult>> entry  : allResults.entrySet()) {
			for (IResult iResult : entry.getValue()) {
				processResult(iResult);
			}
		}
		return getTestResultFromCategory(m_Category);
	}

	private void processResult(IResult iResult) {
		if (iResult instanceof SyntaxErrorResult) {
			m_Category = AutomataScriptTestResultCategory.SYNTAX_ERROR;
		} else if (iResult instanceof IResultWithSeverity) {
			IResultWithSeverity irws = (IResultWithSeverity) iResult;
			throw new AssertionError("not yet implemented");
		}
		throw new AssertionError("not yet implemented");
	}

	@Override
	public TestResult getTestResult(IUltimateServiceProvider services,
			Throwable e) {
		m_Category = AutomataScriptTestResultCategory.EXCEPTION_OR_ERROR;
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
	
	private TestResult getTestResultFromCategory(AutomataScriptTestResultCategory category) {
		switch (category) {
		case ALL_HOLD:
		case ALL_HOLD_TRIVIALLY:
			return TestResult.SUCCESS;
		case EXCEPTION_OR_ERROR:
		case SOME_FAIL:
			return TestResult.FAIL;
		case TIMEOUT:
			return TestResult.UNKNOWN;
		default:
			throw new AssertionError();
		}
	}

}
