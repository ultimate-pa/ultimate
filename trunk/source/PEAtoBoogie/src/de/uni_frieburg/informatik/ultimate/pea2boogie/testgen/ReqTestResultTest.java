package de.uni_frieburg.informatik.ultimate.pea2boogie.testgen;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;

public final class ReqTestResultTest implements IResult{

	final List<TestStep> mTestSteps;
	final String mName;

	public ReqTestResultTest(List<TestStep> testSteps, final String name) {
		mTestSteps = testSteps;
		mName = name;
	}

	@Override
	public String getPlugin() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getShortDescription() {
		return "Found Test for " + mName;
	}

	@Override
	public String getLongDescription() {
		final StringBuilder resultString = new StringBuilder();
		for(final TestStep step: mTestSteps) {
			resultString.append(step.toString());
		}
		return resultString.toString();
	}

}
