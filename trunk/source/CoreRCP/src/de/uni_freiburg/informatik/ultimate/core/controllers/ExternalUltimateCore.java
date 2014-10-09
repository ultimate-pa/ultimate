package de.uni_freiburg.informatik.ultimate.core.controllers;

import java.io.File;
import java.util.concurrent.Semaphore;

import org.apache.log4j.Logger;
import org.eclipse.equinox.app.IApplication;

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

	private final Semaphore mUltimateExit;
	private final Semaphore mStarterContinue;
	private final IController mController;

	protected ManualReleaseToolchainJob mJob;

	public ExternalUltimateCore(IController controller) {
		mUltimateExit = new Semaphore(0);
		mStarterContinue = new Semaphore(0);
		mController = controller;
	}

	public void runUltimate() throws Throwable {
		if (mCurrentUltimateInstance != null) {
			throw new Exception("You must call complete() before re-using this instance ");
		}
		mCurrentUltimateInstance = new UltimateCore();
		mUltimateThrowable = null;

		Thread t = new Thread(new Runnable() {
			@Override
			public void run() {
				try {
					mCurrentUltimateInstance.start(mController, false);
				} catch (Throwable e) {
					mUltimateThrowable = e;
				}
			}
		}, "ActualUltimateInstance");

		t.start();
		mStarterContinue.acquireUninterruptibly();
		if (mUltimateThrowable != null) {
			throw mUltimateThrowable;
		}
	}

	public int init(ICore core, ILoggingService loggingService) {
		return init(core, loggingService, null, 0, null, null);
	}

	public int init(ICore core, ILoggingService loggingService, File inputFile) {
		return init(core, loggingService, null, 0, inputFile, null);
	}

	public int init(ICore core, ILoggingService loggingService, File settingsFile, long deadline, File inputFile,
			PreludeProvider prelude) {
		if (core == null || loggingService == null) {
			return -1;
		}

		Logger logger = getLogger(loggingService);

		if (settingsFile != null) {
			core.loadPreferences(settingsFile.getAbsolutePath());
		}

		try {
			mJob = getToolchainJob(core, mController, logger, inputFile, prelude);
			if (deadline > 0) {
				mJob.setDeadline(deadline);
			}
			mJob.schedule();
			mJob.join();

		} catch (InterruptedException e) {
			logger.error("Exception in Toolchain", e);
			return -1;
		} finally {
			mStarterContinue.release();
			mUltimateExit.acquireUninterruptibly();
		}
		return IApplication.EXIT_OK;
	}

	protected Logger getLogger(ILoggingService loggingService) {
		return loggingService.getControllerLogger();
	}

	protected ManualReleaseToolchainJob getToolchainJob(ICore core, IController controller, Logger logger,
			File inputFile, PreludeProvider prelude) {
		return new ManualReleaseToolchainJob("Processing Toolchain", core, controller, logger, inputFile, prelude);
	}

	public void complete() {
		mJob.releaseToolchainManually();
		mUltimateExit.release();
	}

	protected class ManualReleaseToolchainJob extends DefaultToolchainJob {

		public ManualReleaseToolchainJob(String name, ICore core, IController controller, Logger logger, File input,
				PreludeProvider preludefile) {
			super(name, core, controller, logger, input, preludefile);
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
