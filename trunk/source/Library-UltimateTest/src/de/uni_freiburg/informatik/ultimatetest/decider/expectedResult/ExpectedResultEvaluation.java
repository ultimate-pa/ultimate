package de.uni_freiburg.informatik.ultimatetest.decider.expectedResult;

import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;

public interface ExpectedResultEvaluation<OVERALL_RESULT> {
	
	public enum EvaluationStatus {
		UNKNOWN,
		DETERMINED,
		ERROR
	}

	public void evaluateExpectedResult(UltimateRunDefinition ultimateRunDefinition);
	
	public ExpectedResultEvaluation.EvaluationStatus getExpectedResultEvaluationStatus();
	
	public String getExpectedResultEvaluationMessage();
	
	public OVERALL_RESULT getExpectedResult();
}