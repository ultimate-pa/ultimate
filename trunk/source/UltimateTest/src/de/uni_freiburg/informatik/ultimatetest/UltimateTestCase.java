package de.uni_freiburg.informatik.ultimatetest;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.junit_helper.testfactory.FactoryTestMethod;
import de.uni_freiburg.informatik.ultimate.util.ExceptionUtils;
import static org.junit.Assert.fail;

public class UltimateTestCase {
	private String mName;
	private UltimateStarter mStarter;
	private ITestResultDecider mDecider;
	private Logger mLogger;

	public UltimateTestCase(UltimateStarter starter,
			ITestResultDecider decider, String name) {
		mLogger = Logger.getLogger(UltimateStarter.class);
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
			success = !mDecider.isResultFail(e);
			mLogger.fatal(String.format(
					"There was an exception during the execution of Ultimate: %s%n%s", e,
					ExceptionUtils.getStackTrace(e)));
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