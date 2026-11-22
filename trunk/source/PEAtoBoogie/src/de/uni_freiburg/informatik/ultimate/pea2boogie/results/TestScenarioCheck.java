package de.uni_freiburg.informatik.ultimate.pea2boogie.results;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ITestScenarioCheck;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Spec;

/**
 * The check of a TestScenario (TESTSCENARIO_POS, TESTSCENARIO_NEG). Its messages read "TestScenario &lt;id&gt; is ...",
 * not "Requirement &lt;id&gt; is ..." as for the other requirement checks.
 */
public class TestScenarioCheck extends ReqCheck implements ITestScenarioCheck {

	private static final long serialVersionUID = 1L;

	private final Spec mSpec;
	private final String mTestScenarioId;
	// set by the result transformer when the counterexample of a failed TESTSCENARIO_NEG is reported
	private String mFailurePath;

	public TestScenarioCheck(final Spec spec, final String testScenarioId) {
		super(spec, new String[] { testScenarioId }, new String[] { testScenarioId });
		mSpec = spec;
		mTestScenarioId = testScenarioId;
	}

	@Override
	public String getPositiveMessage() {
		return "TestScenario " + mTestScenarioId + " is " + mSpec.getDefaultPositiveMessage();
	}

	@Override
	public String getNegativeMessage() {
		return "TestScenario " + mTestScenarioId + " is " + mSpec.getDefaultNegativeMessage();
	}

	@Override
	public String getTestScenarioId() {
		return mTestScenarioId;
	}

	@Override
	public String getFailurePath() {
		return mFailurePath;
	}

	@Override
	public void setFailurePath(final String failurePath) {
		mFailurePath = failurePath;
	}
}
