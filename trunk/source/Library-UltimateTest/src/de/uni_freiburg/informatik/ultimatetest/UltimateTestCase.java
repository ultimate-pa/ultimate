package de.uni_freiburg.informatik.ultimatetest;

import static org.junit.Assert.fail;

import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.junit_helper.testfactory.FactoryTestMethod;
import de.uni_freiburg.informatik.ultimate.util.ExceptionUtils;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;

/**
 * @author dietsch
 * 
 */
public class UltimateTestCase {

	private String mName;
	private UltimateRunDefinition m_UltimateRunDefinition;
	private UltimateStarter mStarter;
	private ITestResultDecider mDecider;
	private List<ITestSummary> mSummaries;
	private Logger mLogger;

	public UltimateTestCase(UltimateStarter starter, ITestResultDecider decider, List<ITestSummary> summaries,
			String name, UltimateRunDefinition ultimateRunDefinition) {
		mLogger = Logger.getLogger(UltimateStarter.class);
		mStarter = starter;
		mName = name;
		mDecider = decider;
		mSummaries = summaries;
		m_UltimateRunDefinition = ultimateRunDefinition;
	}

	@FactoryTestMethod
	public void test() {

		Throwable th = null;

		TestResult result = TestResult.FAIL;

		try {
			mStarter.runUltimate();
			result = mDecider.getTestResult(mStarter.getServices().getResultService());
		} catch (Throwable e) {
			th = e;
			result = mDecider.getTestResult(mStarter.getServices().getResultService(), e);
			mLogger.fatal(String.format("There was an exception during the execution of Ultimate: %s%n%s", e,
					ExceptionUtils.getStackTrace(e)));
		} finally {

			boolean success = mDecider.getJUnitTestResult(result);

			if (mSummaries != null) {
				for (ITestSummary summary : mSummaries) {
					summary.addResult(result, mDecider.getResultCategory(), m_UltimateRunDefinition,
							mDecider.getResultMessage(), mStarter.getServices().getResultService());
				}
			}
			mStarter.complete();

			if (!success) {
				String message = mDecider.getResultMessage();
				if (message == null) {
					message = "ITestResultDecider provided no message";
				}
				if (th != null) {
					message += " (Ultimate threw an Exception: " + th.getMessage() + ")";
				}
				fail(message);
			}
		}
	}

	@Override
	public String toString() {
		return mName;
		// return m_UltimateRunDefinition.toString();
	}
}