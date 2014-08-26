package de.uni_freiburg.informatik.ultimatetest.decider.overallResult;

/**
 * The overall result of a software model checker that analyzes safety (e.g., 
 * TraceAbstraction toolchain, Kojak toolchain) is one of this enum's elements.
 * 
 * We may extends this enum in the future.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public enum SafetyCheckerOverallResult {
	SAFE, 
	UNSAFE, 
	UNKNOWN, 
	SYNTAX_ERROR, 
	TIMEOUT, 
	UNSUPPORTED_SYNTAX, 
	EXCEPTION_OR_ERROR, 
	NO_RESULT;
}

