package de.uni_freiburg.informatik.ultimate.pea2boogie.testgen;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.pea2boogie.Activator;

public final class ReqTestResultTest implements IResult {

	final List<TestStep> mTestSteps;
	final String mName;

	public ReqTestResultTest(final List<TestStep> testSteps, final String name) {
		mTestSteps = testSteps;
		mName = name;
	}

	public List<TestStep> getTestSteps() {
		return Collections.unmodifiableList(mTestSteps);
	}

	@Override
	public String getPlugin() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public String getShortDescription() {
		return "Found Test for " + mName;
	}

	@Override
	public String getLongDescription() {
		final StringBuilder resultString = new StringBuilder();
		for (final TestStep step : mTestSteps) {
			resultString.append(step.toString());
		}
		return resultString.toString();
	}
}
