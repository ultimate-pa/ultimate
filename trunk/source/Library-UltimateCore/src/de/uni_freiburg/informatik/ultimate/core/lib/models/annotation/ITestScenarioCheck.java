package de.uni_freiburg.informatik.ultimate.core.lib.models.annotation;

/**
 * A check that belongs to a requirements TestScenario. Lets the TestScenario summary read it without depending on the
 * plug-in that created it.
 */
public interface ITestScenarioCheck {

	/**
	 * @return the id of the TestScenario this check belongs to
	 */
	String getTestScenarioId();

	/**
	 * @return the run on which a failed "trace is forbidden to hold" TestScenario happens (variable values per time
	 *         interval), set when its counterexample is reported, or null
	 */
	String getFailurePath();

	void setFailurePath(String failurePath);
}
