package de.uni_freiburg.informatik.ultimate.test.decider.overallresult;

/**
 * If we want to say in one word what the result of a TreeAutomizer run was, it should be one of the following.
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public enum TreeAutomizerOverallResult {
	SAT,
	UNSAT,
	UNKNOWN,
	CRASH,
	TIMEOUT
}
