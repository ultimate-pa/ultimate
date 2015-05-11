package de.uni_freiburg.informatik.ultimate.core.controllers;

import java.io.File;
import java.util.concurrent.Semaphore;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.IStatus;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.UltimateCore;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.DefaultToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.services.ILoggingService;
import de.uni_freiburg.informatik.ultimate.core.services.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;

/**
 * 
 * Note: Not thread-safe (will build another one which is thread-safe and keeps
 * one UltimateCore instance)
 * 
 * <ol>
 * <li>{@link #runUltimate()}</li>
 * <li>Delegate your callback to
 * {@link IController#init(ICore, ILoggingService)} to
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
	private final IController mController;

	protected ManualReleaseToolchainJob mJob;

	private volatile int mReturnStatus;

	public ExternalUltimateCore(IController controller) {
		mUltimateExit = new Semaphore(0);
		mStarterContinue = new Semaphore(0);
		mController = controller;
		mReachedInit = false;
	}

	public Object runUltimate() throws Throwable {
		if (mCurrentUltimateInstance != null) {
			throw new Exception("You must call complete() before re-using this instance ");
		}
		mCurrentUltimateInstance = new UltimateCore();
		mUltimateThrowable = null;

		final ActualUltimateRunnable runnable = new ActualUltimateRunnable();

		Thread thread = new Thread(runnable, "ActualUltimateInstance");

		thread.start();
		mStarterContinue.acquireUninterruptibly();
		if (mUltimateThrowable != null) {
			throw mUltimateThrowable;
		}
		Object rtr = runnable.getReturnStatus();
		mReturnStatus = (int) rtr;
		return rtr;
	}

	public int init(ICore core, ILoggingService loggingService) {
		return init(core, loggingService, null, 0, null, null);
	}

	public int init(ICore core, ILoggingService loggingService, File[] inputFiles) {
		return init(core, loggingService, null, 0, inputFiles, null);
	}

	public int init(ICore core, ILoggingService loggingService, File settingsFile, long deadline, File[] inputFiles,
			PreludeProvider prelude) {
		Logger logger = null;
		try {
			mReachedInit = true;
			if (core == null || loggingService == null) {
				return IStatus.ERROR;
			}

			logger = getLogger(loggingService);

			if (settingsFile != null) {
				core.loadPreferences(settingsFile.getAbsolutePath());
			}
			mJob = getToolchainJob(core, mController, logger, inputFiles, prelude);
			if (deadline > 0) {
				mJob.setDeadline(deadline);
			}
			mJob.schedule();
			mJob.join();

		} catch (Throwable e) {
			logger.error("Exception during toolchain execution.", e);
			return IStatus.ERROR;
		} finally {
			mStarterContinue.release();
			mUltimateExit.acquireUninterruptibly();
		}
		return mReturnStatus;
	}

	protected Logger getLogger(ILoggingService loggingService) {
		return loggingService.getControllerLogger();
	}

	protected ManualReleaseToolchainJob getToolchainJob(ICore core, IController controller, Logger logger,
			File[] inputFiles, PreludeProvider prelude) {
		return new ManualReleaseToolchainJob("Processing Toolchain", core, controller, logger, inputFiles, prelude);
	}

	public void complete() {
		if (mJob != null) {
			// mJob may be null if Ultimate did not complete its init phase
			mJob.releaseToolchainManually();
		}
		mUltimateExit.release();
	}

	private final class ActualUltimateRunnable implements Runnable {
		private Object mReturnStatus;

		private ActualUltimateRunnable() {
			mReturnStatus = null;
		}

		@Override
		public void run() {
			try {
				mReturnStatus = mCurrentUltimateInstance.start(mController, false);
			} catch (Throwable e) {
				mUltimateThrowable = e;
			}

			if (!mReachedInit) {
				if (mUltimateThrowable == null) {
					mUltimateThrowable = new LivecycleException(
							"Ultimate terminated before calling init(...) on ExternalUltimateCore");
				}
				mStarterContinue.release();
			}
		}

		private Object getReturnStatus() {
			return mReturnStatus == null ? IStatus.ERROR : mReturnStatus;
		}
	}

	protected class ManualReleaseToolchainJob extends DefaultToolchainJob {

		public ManualReleaseToolchainJob(String name, ICore core, IController controller, Logger logger, File[] inputs,
				PreludeProvider preludefile) {
			super(name, core, controller, logger, inputs, preludefile);
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
