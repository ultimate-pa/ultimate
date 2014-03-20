package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.io.File;

import de.uni_freiburg.informatik.ultimatetest.decider.SafetyCheckTestResultDecider;

public class TraceAbstractionTestResultDecider extends SafetyCheckTestResultDecider {

	public TraceAbstractionTestResultDecider(File inputFile) {
		super(inputFile);
	}

	@Override
	public boolean getJUnitTestResult(TestResult actualResult) {
		// Matthias wants to see Unknown results as success
		switch (actualResult) {
		case FAIL:
			return false;
		case SUCCESS:
		case UNKNOWN:
			return true;
		default:
			throw new IllegalArgumentException("actualResult has an unknown value");
		}
	}

}
