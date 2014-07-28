package de.uni_freiburg.informatik.ultimatetest;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.junit_helper.testfactory.FactoryTestMethod;
import de.uni_freiburg.informatik.ultimate.util.ExceptionUtils;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;
import static org.junit.Assert.fail;

/**
 * @author dietsch
 * 
 */
public class UltimateTestCase {

	private String mName;
	private String mFileName;
	private UltimateStarter mStarter;
	private ITestResultDecider mDecider;
	private ITestSummary mSummary;
	private Logger mLogger;

	public UltimateTestCase(UltimateStarter starter, ITestResultDecider decider, ITestSummary summary, String name,
			String filename) {
		mLogger = Logger.getLogger(UltimateStarter.class);
		mStarter = starter;
		mName = name;
		mDecider = decider;
		mSummary = summary;
		mFileName = filename;
	}

	@FactoryTestMethod
	public void test() {

		TestResult result = TestResult.FAIL;

		try {
			mStarter.runUltimate();
			result = mDecider.getTestResult(mStarter.getServices());
		} catch (Throwable e) {
			result = mDecider.getTestResult(mStarter.getServices(), e);
			mLogger.fatal(String.format("There was an exception during the execution of Ultimate: %s%n%s", e,
					ExceptionUtils.getStackTrace(e)));
		} finally {
			mStarter.complete();

			boolean success = mDecider.getJUnitTestResult(result);

			if (mSummary != null) {
				mSummary.setTestResultDecider(mDecider);
				mSummary.addResult(result, success, mDecider.getResultCategory(), mFileName,
						mDecider.getResultMessage());
			}

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