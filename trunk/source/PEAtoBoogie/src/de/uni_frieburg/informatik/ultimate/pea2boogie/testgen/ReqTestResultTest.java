package de.uni_frieburg.informatik.ultimate.pea2boogie.testgen;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;

public final class ReqTestResultTest implements IResult{

	final List<TestStep> mTestSteps;

	public ReqTestResultTest(List<TestStep> testSteps) {
		mTestSteps = testSteps;
	}

	@Override
	public String getPlugin() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getShortDescription() {
		return "Found Test for TODO";
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
