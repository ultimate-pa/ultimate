/*
 * Copyright (C) 2021 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.coreplugin.services;

import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

import org.hamcrest.MatcherAssert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.IToolchainProgressMonitor;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainCancel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/***
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ProgressMonitorTest {

	private IUltimateServiceProvider mServices;
	private ILogger mLogger;
	private ProgressMonitorService mPms;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock(LogLevel.DEBUG);
		mLogger = mServices.getLoggingService().getLogger(getClass());
		final IToolchainProgressMonitor monitor = new IToolchainProgressMonitorMock();
		final IToolchainCancel cancel = new IToolchainCancelMock();
		mPms = new ProgressMonitorService(monitor, mLogger, cancel);
	}

	@Test
	public void testSimpleTimeout() throws InterruptedException {
		final long timeout = 1000;
		final long interval = 50;
		runTimeoutTest(() -> {
			final IProgressAwareTimer pwt = ProgressAwareTimer.createWithTimeout(mPms, timeout);
			while (pwt.continueProcessing()) {
				TimeUnit.MILLISECONDS.sleep(interval);
			}
		}, timeout, interval);
	}

	@Test
	public void testChildTimeout() throws InterruptedException {
		final long timeout = 1000;
		final long interval = 50;
		runTimeoutTest(() -> {
			final IProgressAwareTimer pwt = mPms.getChildTimer(timeout);
			while (pwt.continueProcessing()) {
				TimeUnit.MILLISECONDS.sleep(interval);
			}
		}, timeout, interval);
	}

	@Test
	public void testNestedTimeoutChild() throws InterruptedException {
		final long timeout = 1000;
		final long interval = 50;
		runTimeoutTest(() -> {
			final IProgressAwareTimer pwt = mPms.getChildTimer(timeout * 10);
			final IUltimateServiceProvider services = mPms.registerChildTimer(mServices, pwt);
			final IProgressAwareTimer child = services.getProgressMonitorService().getChildTimer(0.1);
			final IUltimateServiceProvider childServices =
					services.getProgressMonitorService().registerChildTimer(services, child);
			while (childServices.getProgressMonitorService().continueProcessing()) {
				TimeUnit.MILLISECONDS.sleep(interval);
			}
		}, timeout, interval);
	}

	@Test
	public void testNestedTimeoutParent() throws InterruptedException {
		final long timeout = 1000;
		final long interval = 50;
		runTimeoutTest(() -> {
			final IProgressAwareTimer pwt = mPms.getChildTimer(timeout);
			final IUltimateServiceProvider services = mPms.registerChildTimer(mServices, pwt);
			final IProgressAwareTimer child = services.getProgressMonitorService().getChildTimer(timeout * 10);
			final IUltimateServiceProvider childServices =
					services.getProgressMonitorService().registerChildTimer(services, child);
			while (childServices.getProgressMonitorService().continueProcessing()) {
				TimeUnit.MILLISECONDS.sleep(interval);
			}
		}, timeout, interval);
	}

	@Test
	public void testNestedTimeoutNoLayerParent() throws InterruptedException {
		final long timeout = 1000;
		final long interval = 50;
		runTimeoutTest(() -> {
			final IProgressAwareTimer pwt = mPms.getChildTimer(timeout);
			final IProgressAwareTimer child = pwt.getChildTimer(timeout * 10);
			while (child.continueProcessing()) {
				TimeUnit.MILLISECONDS.sleep(interval);
			}
		}, timeout, interval);
	}

	@Test
	public void testNestedTimeoutNoLayerChild() throws InterruptedException {
		final long timeout = 1000;
		final long interval = 50;
		runTimeoutTest(() -> {
			final IProgressAwareTimer pwt = mPms.getChildTimer(timeout * 10);
			final IProgressAwareTimer child = pwt.getChildTimer(timeout);
			while (child.continueProcessing()) {
				TimeUnit.MILLISECONDS.sleep(interval);
			}
		}, timeout, interval);
	}

	@Test
	public void testNestedTimeoutNoLayerChildPercentage() throws InterruptedException {
		final long timeout = 1000;
		final long interval = 50;
		runTimeoutTest(() -> {
			final IProgressAwareTimer pwt = mPms.getChildTimer(timeout * 10);
			final IProgressAwareTimer child = pwt.getChildTimer(0.1);
			while (child.continueProcessing()) {
				TimeUnit.MILLISECONDS.sleep(interval);
			}
		}, timeout, interval);
	}

	private void runTimeoutTest(final IFun fun, final long timeout, final long interval) throws InterruptedException {
		final long start = System.currentTimeMillis();
		fun.run();
		final long stop = System.currentTimeMillis();
		final long timeoutTime = stop - start;
		final long grace = timeout + interval * 2;
		MatcherAssert.assertThat("Timeout took more than " + grace + "ms", timeoutTime < grace);
		MatcherAssert.assertThat("Timeout took less than " + timeout + "ms", timeoutTime >= timeout);
		mLogger.info("Took %s ms to timeout", timeoutTime);
	}

	@FunctionalInterface
	public interface IFun {
		void run() throws InterruptedException;
	}

	private static final class IToolchainCancelMock implements IToolchainCancel {

		private final CountDownLatch mLatch = new CountDownLatch(1);

		@Override
		public CountDownLatch cancelToolchain() {
			return mLatch;
		}
	}

	private static final class IToolchainProgressMonitorMock implements IToolchainProgressMonitor {

		private boolean mIsCanceled = false;

		@Override
		public void worked(final int work) {
			// do nothing
		}

		@Override
		public void subTask(final String name) {
			// do nothing
		}

		@Override
		public void setTaskName(final String name) {
			// do nothing
		}

		@Override
		public void setCanceled(final boolean value) {
			mIsCanceled = value;
		}

		@Override
		public boolean isCanceled() {
			return mIsCanceled;
		}

		@Override
		public void internalWorked(final double work) {
			// do nothing
		}

		@Override
		public void done() {
			// do nothing
		}

		@Override
		public void beginTask(final String name, final int totalWork) {
			// do nothing
		}
	}

}
