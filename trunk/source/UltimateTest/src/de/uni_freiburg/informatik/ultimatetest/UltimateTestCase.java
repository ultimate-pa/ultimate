package de.uni_freiburg.informatik.ultimatetest;

import de.uni_freiburg.informatik.junit_helper.testfactory.FactoryTestMethod;
import static org.junit.Assert.fail;

public class UltimateTestCase {
	private String mName;
	private UltimateStarter mStarter;
	private ITestResultDecider mDecider;

	public UltimateTestCase(UltimateStarter starter,
			ITestResultDecider decider, String name) {
		mStarter = starter;
		mName = name;
		mDecider = decider;
	}

	@FactoryTestMethod
	public void test() {

		boolean success = false;

		try {
			mStarter.runUltimate();
			success = !mDecider.isResultFail();
		} catch (Exception e) {
			e.printStackTrace();
		} finally {
			mStarter.complete();
			if (!success) {
				fail();
			}
		}
	}

	@Override
	public String toString() {
		return mName;
	}
}