package de.uni_freiburg.informatik.ultimatetest.decider.overallResult;

/**
 * The possible overall results of a software model checker that analyzes safety
 * (e.g., TraceAbstraction toolchain, Kojak toolchain) are these enum's elements.
 * 
 * We may extends this enum in the future.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public enum SafetyCheckerOverallResult {
	SAFE, 
	UNSAFE,
	UNSAFE_MEMTRACK,
	UNSAFE_DEREF,
	UNSAFE_FREE,
	UNKNOWN, 
	SYNTAX_ERROR, 
	TIMEOUT, 
	UNSUPPORTED_SYNTAX, 
	EXCEPTION_OR_ERROR, 
	NO_RESULT;
}

