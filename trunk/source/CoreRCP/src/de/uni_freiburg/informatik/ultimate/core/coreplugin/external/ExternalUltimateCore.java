/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.coreplugin.external;

import java.io.File;
import java.util.concurrent.Semaphore;
import java.util.concurrent.TimeUnit;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.UltimateCore;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.LifecycleException;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.DefaultToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.model.IController;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILoggingService;

/**
 *
 * Note: Not thread-safe (will build another one which is thread-safe and keeps one UltimateCore instance)
 *
 * <ol>
 * <li>{@link #runUltimate()}</li>
 * <li>Delegate your callback to {@link IController#init(ICore, ILoggingService)} to
 * {@link #init(ICore, ILoggingService, File)}, which will start a toolchain</li>
 * <li>Get results or whatever you want</li>
 * <li>Call {@link #complete()}</li>
 * <li>Throw this instance away</li>
 * </ol>
 *
 * @author dietsch
 *
 */
public class ExternalUltimateCore {

	private UltimateCore mCurrentUltimateInstance;
	private Throwable mUltimateThrowable;
	private volatile boolean mReachedInit;

	private final Semaphore mUltimateExit;
	private final Semaphore mStarterContinue;
	private final IController<RunDefinition> mController;

	protected ManualReleaseToolchainJob mJob;

	private volatile IStatus mReturnStatus;

	public ExternalUltimateCore(final IController<RunDefinition> controller) {
		mUltimateExit = new Semaphore(0);
		mStarterContinue = new Semaphore(0);
		mController = controller;
		mReachedInit = false;
	}

	public IStatus runUltimate() throws Throwable {
		if (mCurrentUltimateInstance != null) {
			throw new Exception("You must call complete() before re-using this instance ");
		}
		mCurrentUltimateInstance = new UltimateCore();
		mUltimateThrowable = null;

		final ActualUltimateRunnable runnable = new ActualUltimateRunnable();

		final Thread thread = new Thread(runnable, "ActualUltimateInstance");

		thread.start();
		// Try to acquire for 10 seconds, just to make sure everything is there.
		if (!mStarterContinue.tryAcquire(10, TimeUnit.SECONDS)) {
			final IPreferenceProvider prefs = mCurrentUltimateInstance.getPreferenceProvider(Activator.PLUGIN_ID);
			if (prefs == null) {
				throw new LifecycleException("Could not initialize preferences in given time frame.");
			}

			final long timeout = prefs.getLong(CorePreferenceInitializer.LABEL_TIMEOUT);

			if (!mStarterContinue.tryAcquire(timeout, TimeUnit.MILLISECONDS)) {
				// mCurrentUltimateInstance.cancelToolchain();
				// Die after 5 seconds definitely
				if (!mStarterContinue.tryAcquire(5, TimeUnit.SECONDS)) {
					throw new LifecycleException("Timeout elapsed but Ultimate did not shut down.");
				}
			}
		}

		// mStarterContinue.acquireUninterruptibly();
		if (mUltimateThrowable != null) {
			throw mUltimateThrowable;
		}
		return mReturnStatus;
	}

	public IStatus init(final ICore<RunDefinition> core) {
		return init(core, null, 0, null);
	}

	public IStatus init(final ICore<RunDefinition> core, final File[] inputFiles) {
		return init(core, null, 0, inputFiles);
	}

	public IStatus init(final ICore<RunDefinition> core, final File settingsFile, final long deadline,
			final File[] inputFiles) {
		ILogger logger = null;
		try {
			mReachedInit = true;
			if (core == null) {
				return new Status(IStatus.ERROR, Activator.PLUGIN_ID, IStatus.ERROR, "Initialization failed", null);
			}

			logger = getLogger(core.getCoreLoggingService());

			if (settingsFile != null) {
				core.loadPreferences(settingsFile.getAbsolutePath());
			}
			mJob = getToolchainJob(core, mController, logger, inputFiles);
			if (deadline > 0) {
				mJob.setDeadline(deadline);
			}
			mJob.schedule();
			mJob.join();
			mReturnStatus = mJob.getResult();
		} catch (final Throwable e) {
			logger.error("Exception during toolchain execution.", e);
		} finally {
			mStarterContinue.release();
			mUltimateExit.acquireUninterruptibly();
		}
		return mReturnStatus;
	}

	protected ILogger getLogger(final ILoggingService loggingService) {
		return loggingService.getControllerLogger();
	}

	protected ManualReleaseToolchainJob getToolchainJob(final ICore<RunDefinition> core,
			final IController<RunDefinition> controller, final ILogger logger, final File[] inputFiles) {
		return new ManualReleaseToolchainJob("Processing Toolchain", core, controller, logger, inputFiles);
	}

	public void complete() {
		if (mJob != null) {
			// mJob may be null if Ultimate did not complete its init phase
			mJob.releaseToolchainManually();
		}
		mUltimateExit.release();
	}

	private final class ActualUltimateRunnable implements Runnable {

		@Override
		public void run() {
			try {
				mCurrentUltimateInstance.startManually(mController);
			} catch (final Throwable e) {
				mUltimateThrowable = e;
			}

			if (!mReachedInit) {
				if (mUltimateThrowable == null) {
					mUltimateThrowable = new LifecycleException(
							"Ultimate terminated before calling init(...) on ExternalUltimateCore");
				}
				mStarterContinue.release();
			}
		}
	}

	protected class ManualReleaseToolchainJob extends DefaultToolchainJob {

		public ManualReleaseToolchainJob(final String name, final ICore<RunDefinition> core,
				final IController<RunDefinition> controller, final ILogger logger, final File[] inputs) {
			super(name, core, controller, logger, inputs);
		}

		@Override
		protected void releaseToolchain() {
			// we use a manual release
		}

		public void releaseToolchainManually() {
			super.releaseToolchain();
		}

	}

}
