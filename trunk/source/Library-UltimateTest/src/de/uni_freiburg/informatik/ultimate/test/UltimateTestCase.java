/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE UnitTest Library.
 *
 * The ULTIMATE UnitTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE UnitTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE UnitTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE UnitTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE UnitTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.test;

import java.util.List;
import java.util.function.Function;

import org.eclipse.core.runtime.IStatus;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.LifecycleException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.FactoryTestMethod;
import de.uni_freiburg.informatik.ultimate.test.mocks.ConsoleLogger;
import de.uni_freiburg.informatik.ultimate.test.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestLogfile;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class UltimateTestCase implements Comparable<UltimateTestCase> {

	private static final AfterTest NOOP = new AfterTest() {
		@Override
		public void afterTest() {
			// do nothing
		}
	};

	private final String mName;
	private final UltimateRunDefinition mUltimateRunDefinition;
	private final ConsoleLogger mTestLogger;

	private boolean mHasStarted;
	private List<ITestLogfile> mLogs;
	private ITestResultDecider mDecider;
	private AfterTest mFunAfterTest;

	private final Function<IUltimateServiceProvider, IUltimateServiceProvider> mServicesCallback;

	public UltimateTestCase(final ITestResultDecider decider, final UltimateRunDefinition urd,
			final List<ITestLogfile> logs,
			final Function<IUltimateServiceProvider, IUltimateServiceProvider> servicesCallback) {
		if (urd == null) {
			throw new IllegalArgumentException("ultimateRunDefinition");
		}
		mServicesCallback = servicesCallback;

		mDecider = decider;
		mLogs = logs;

		mName = urd.toString();
		mUltimateRunDefinition = urd;
		mTestLogger = new ConsoleLogger();
		mHasStarted = false;
		if (urd.getAfterTestMethod() == null) {
			mFunAfterTest = NOOP;
		} else {
			mFunAfterTest = urd.getAfterTestMethod();
		}
	}

	@FactoryTestMethod
	public void test() {
		if (mHasStarted) {
			throw new UltimateTestFailureException("Can run a test only once");
		}
		mHasStarted = true;

		// call the garbage collector before starting a new test
		System.gc();
		System.runFinalization();
		System.gc();
		Runtime.getRuntime().gc();

		// start debug code: use this only in controlled situations!
		// try {
		// Thread.sleep(500);
		// } catch (final InterruptedException e1) {
		// }
		// HeapDumper.dumpHeap("C:\\Installed\\mat\\dumps\\", false);
		// end debug code

		Throwable th = null;
		TestResult result = TestResult.FAIL;
		boolean livecycleFailure = false;
		final UltimateStarter starter = new UltimateStarter(mUltimateRunDefinition, mServicesCallback);

		try {
			updateLogsPre();
			final String deciderName = mDecider.getClass().getSimpleName();
			final IStatus returnCode = starter.runUltimate();
			// logging service is only available after runUltimate() has been called
			final ILogger logger = getLoggerFromStarter(starter);
			logger.info("Deciding this test: " + deciderName);
			result = mDecider.getTestResult(starter.getServices());
			if (!returnCode.isOK() && result != TestResult.FAIL) {
				logger.fatal("#################### Overwriting decision of " + deciderName
						+ " and setting test status to FAIL ####################");
				logger.fatal("Ultimate returned an unexpected status:");
				logger.fatal("Code      " + returnCode.getCode());
				logger.fatal("Severity  " + returnCode.getSeverity());
				logger.fatal("Message   " + returnCode.getMessage());
				logger.fatal("Plugin ID " + returnCode.getPlugin());
				if (returnCode.getException() != null) {
					logger.fatal("Exception:", returnCode.getException());
				}
				result = TestResult.FAIL;
			}

		} catch (final LifecycleException lex) {
			// if this happens, mStarter, mLogger, etc. are not initialized
			th = lex;
			result = TestResult.FAIL;
			lex.printStackTrace();
			livecycleFailure = true;
		} catch (final Throwable e) {
			th = e;
			result = mDecider.getTestResult(starter.getServices(), e);
			logWithFreshLogger(starter, e, "There was an exception during the execution of Ultimate");
		} finally {
			boolean success = false;

			if (!livecycleFailure) {
				success = mDecider.getJUnitSuccess(result);
			}

			final String resultMessage = mDecider.getResultMessage();
			final String resultCategory = mDecider.getResultCategory();

			try {
				updateLogsPost(starter.getServices(), result, resultCategory, resultMessage);
			} catch (final Throwable ex) {
				logWithFreshLogger(starter, ex,
						"There was an exception during the writing of summary or log information");
				throw ex;
			}

			starter.complete();

			mDecider = null;
			mLogs = null;

			if (!success) {
				String message = null;

				if (!livecycleFailure) {
					message = resultMessage;
				}

				if (message == null) {
					message = "ITestResultDecider provided no message";
				}
				if (th != null) {
					message += " (Ultimate threw an Exception: " + th.getMessage() + ")";
					failTest(message, th);
				} else {
					failTest(message);
				}
			}

			try {
				mFunAfterTest.afterTest();
			} catch (final Throwable ex) {
				logWithFreshLogger(starter, ex, "There was an exception during execution of after-test method");
			}
			mFunAfterTest = null;
		}
	}

	private static ILogger getLoggerFromStarter(final UltimateStarter starter) {
		if (starter.getServices() == null) {
			return new ConsoleLogger();
		}
		return starter.getServices().getLoggingService().getLogger(UltimateStarter.class);
	}

	private static void logWithFreshLogger(final UltimateStarter starter, final Throwable ex, final String message) {
		getLoggerFromStarter(starter).fatal(String.format(message + ": %s%n%s", ex, CoreUtil.getStackTrace(ex)));
	}

	private void updateLogsPre() {
		if (mLogs == null) {
			return;
		}
		mLogs.stream().filter(a -> a instanceof IIncrementalLog).map(a -> (IIncrementalLog) a)
				.forEach(a -> a.addEntryPreStart(mUltimateRunDefinition, mTestLogger));
	}

	private void updateLogsPost(final IUltimateServiceProvider services, final TestResult result,
			final String resultCategory, final String resultMessage) {
		if (mLogs == null) {
			return;
		}

		IResultService rservice = null;
		if (services != null) {
			rservice = services.getResultService();
			assert rservice != null : "Could not retrieve ResultService";
		}

		for (final ITestLogfile log : mLogs) {
			if (log instanceof IIncrementalLog) {
				((IIncrementalLog) log).addEntryPostCompletion(mUltimateRunDefinition, result, resultCategory,
						resultMessage, services, mTestLogger);
			}
			if (log instanceof ITestSummary) {
				((ITestSummary) log).addResult(mUltimateRunDefinition, result, resultCategory, resultMessage, mName,
						rservice);
			}
		}
	}

	public UltimateRunDefinition getUltimateRunDefinition() {
		return mUltimateRunDefinition;
	}

	@Override
	public String toString() {
		return mName;
	}

	private static void failTest(final String message) throws UltimateTestFailureException {
		final UltimateTestFailureException exception = new UltimateTestFailureException(message);
		final StackTraceElement elem = new StackTraceElement(UltimateTestCase.class.getPackage().getName(), "test",
				"UltimateTestCase.java", -1);
		exception.setStackTrace(new StackTraceElement[] { elem });
		throw exception;
	}

	private static void failTest(final String message, final Throwable th) throws UltimateTestFailureException {
		final UltimateTestFailureException exception = new UltimateTestFailureException(message, th);
		final StackTraceElement elem = new StackTraceElement(UltimateTestCase.class.getPackage().getName(), "test",
				"UltimateTestCase.java", -1);
		exception.setStackTrace(new StackTraceElement[] { elem });
		throw exception;
	}

	@Override
	public int compareTo(final UltimateTestCase o) {
		return mUltimateRunDefinition.compareTo(o.mUltimateRunDefinition);
	}

	/**
	 * A method that can be executed after a test.
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	@FunctionalInterface
	public interface AfterTest {

		public void afterTest();
	}
}
