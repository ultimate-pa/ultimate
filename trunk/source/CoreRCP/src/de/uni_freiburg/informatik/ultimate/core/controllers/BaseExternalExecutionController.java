package de.uni_freiburg.informatik.ultimate.core.controllers;

import org.apache.log4j.Logger;
import org.eclipse.equinox.app.IApplication;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.UltimateCore;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.BasicToolchainJob;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;

/**
 * 
 * This class simplifies the construction of controllers for external execution
 * of Ultimate (i.e. if you do not want to control the core thread by yourself).
 * 
 * It works like this:
 * <ul>
 * <li>UltimateCore is initialized with an instance of this class</li>
 * <li>UltimateCore is started in its own thread via {@link #startUltimate()}</li>
 * <li>UltimateCore calls back to this instance to {@link #init(ICore)}</li>
 * <li>{@link #init(ICore)} blocks until someone calls {@link #nextRun()}</li>
 * <li>After call to {@link #nextRun()}, {@link #init(ICore)} will call
 * {@link #createAndRunToolchainJob()}, where you hopefully implemented some
 * kind of initialization for a {@link BasicToolchainJob} instance, which you
 * then start (e.g. schedule)</li>
 * <li>After {@link #createAndRunToolchainJob()} returns, control stays in
 * {@link #init(ICore)} until {@link #nextRun()} or {@link #close()} is called.
 * The later makes this instance unusable, you should throw it away afterwards.</li>
 * </ul>
 * 
 * @author dietsch
 */
public abstract class BaseExternalExecutionController implements IController {

	protected Logger mLogger;
	protected ICore mCurrentCoreReference;
	
	private Thread mCoreThread;

	protected UltimateCore mActualCore;
	private Object mLock;

	private boolean mStart;
	private boolean mAbort;

	public BaseExternalExecutionController() {
		mLock = new Object();
		mAbort = false;
	}

	@Override
	public int init(ICore core) {
		if (core == null) {
			return -1;
		}
		mCurrentCoreReference = core;
		mLogger = UltimateServices.getInstance().getLogger(getPluginID());
		
		while (!mAbort) {
			synchronized (mLock) {
				while (!mStart) {
					try {
						mLock.wait();
					} catch (InterruptedException e) {
						e.printStackTrace();
					}
				}
				if (mAbort) {
					break;
				}
				try {
					createAndRunToolchainJob();
				} catch (Throwable e) {
					mLogger.error("Exception in Toolchain", e);
				}
				mStart = false;
				mLock.notifyAll();
			}
		}

		return IApplication.EXIT_OK;
	}

	/**
	 * Will be called after each call to nextRun();
	 * 
	 * @throws Throwable
	 */
	protected abstract void createAndRunToolchainJob() throws Throwable;

	protected void nextRun() {
		synchronized (mLock) {
			mStart = true;
			mLock.notifyAll();
			while (mStart && !mAbort) {
				try {
					mLock.wait();
				} catch (InterruptedException e) {
					e.printStackTrace();
				}
			}
		}
	}
	
	public void startUltimate() {
		if (mCoreThread != null) {
			throw new RuntimeException(
					"Ultimate is already started! Close the current instance, create a new instance, restart");
		}

		if (UltimateServices.getInstance() == null) {
			mActualCore = new UltimateCore();
			UltimateServices.createInstance(mActualCore);
		}
		final IController activeController = this;
		Runnable ultim = new Runnable() {
			@Override
			public void run() {
				try {
					mActualCore.start(activeController, true);
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		};
		mCoreThread = new Thread(ultim);
		mCoreThread.start();
	}

	public void close() {
		synchronized (mLock) {
			mAbort = true;
			mLock.notifyAll();
		}
	}
}
