package de.uni_freiburg.informatik.ultimate.core.util;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.lang.Thread.State;
import java.util.ConcurrentModificationException;
import java.util.concurrent.Semaphore;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;

import org.apache.commons.lang3.StringUtils;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.IStorable;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.ExceptionUtils;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public final class MonitoredProcess implements IStorable {

	private final Logger mLogger;
	private final IToolchainStorage mStorage;
	private final IUltimateServiceProvider mServices;

	private final String mCommand;
	private final String mExitCommand;

	// buffer size in bytes
	private final static int sBufferSize = 2048;
	private final PipedInputStream mStdInStreamPipe;
	private final PipedInputStream mStdErrStreamPipe;
	private final Semaphore mWaitForSetup;

	private Thread mMonitor;
	private int mID;
	private AtomicBoolean mTimeoutAttached;

	private volatile Process mProcess;
	private volatile boolean mProcessCompleted;
	private volatile int mReturnCode;

	private final static AtomicInteger sInstanceCounter = new AtomicInteger();

	private MonitoredProcess(Process process, String command, String exitCommand, IUltimateServiceProvider services,
			IToolchainStorage storage) {
		assert storage != null;
		assert services != null;
		mStorage = storage;
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		mProcess = process;
		mProcessCompleted = false;
		mCommand = command;
		mExitCommand = exitCommand;
		mReturnCode = -1;
		mMonitor = null;
		mStdInStreamPipe = new PipedInputStream(sBufferSize);
		mStdErrStreamPipe = new PipedInputStream(sBufferSize);

		// -2 because we wait until all 3 threads are ready (stderr buffer,
		// stdinbuffer,
		// actual process watcher) before returning from exec
		mWaitForSetup = new Semaphore(-2);
		mTimeoutAttached = new AtomicBoolean(false);
	}

	/**
	 * 
	 * @param command
	 * @return
	 * @throws IOException
	 */
	public static MonitoredProcess exec(String[] command, String workingDir, String exitCommand,
			IUltimateServiceProvider services, IToolchainStorage storage) throws IOException {
		final MonitoredProcess mp;
		String oneLineCmd = StringUtils.join(command, " ");

		if (workingDir != null) {
			mp = new MonitoredProcess(Runtime.getRuntime().exec(command, null, new File(workingDir)), oneLineCmd,
					exitCommand, services, storage);
		} else {
			mp = new MonitoredProcess(Runtime.getRuntime().exec(command), oneLineCmd, exitCommand, services, storage);
		}

		mp.start(workingDir, storage, oneLineCmd);
		return mp;
	}

	/**
	 * Execute a command as process. The process will be cleaned when the
	 * toolchain ends.
	 * 
	 * @param command
	 * @param services
	 * @param storage
	 * @return
	 * @throws IOException
	 */
	public static MonitoredProcess exec(String command, String exitCommand, IUltimateServiceProvider services,
			IToolchainStorage storage) throws IOException {
		return exec(command.split(" "), null, exitCommand, services, storage);
	}

	// public static MonitoredProcess exec(String command,
	// IUltimateServiceProvider services, IToolchainStorage storage)
	// throws IOException {
	// return exec(command, null, services, storage);
	// }

	private void start(String workingDir, IToolchainStorage storage, String oneLineCmd) {
		mID = sInstanceCounter.incrementAndGet();
		storage.putStorable(getKey(mID, oneLineCmd), this);

		mMonitor = new Thread(createProcessRunner(), "MonitoredProcess " + mID + " " + oneLineCmd);
		mLogger.info(String.format("Starting monitored process %s with %s (exit command is %s, workingDir is %s)", mID,
				mCommand, mExitCommand, workingDir));
		mMonitor.start();
		mWaitForSetup.acquireUninterruptibly();
	}

	/**
	 * Wait forever until the process terminates
	 * 
	 * @return A {@link MonitoredProcessState} instance indicating whether the
	 *         process is still running or not and if not, what the return code
	 *         is
	 * @throws InterruptedException
	 */
	public MonitoredProcessState waitfor() throws InterruptedException {
		if (mMonitor.getState().equals(State.TERMINATED)) {
			return new MonitoredProcessState(false, false, mReturnCode);
		}
		mMonitor.join();
		if (mMonitor.getState().equals(State.TERMINATED)) {
			return new MonitoredProcessState(false, false, mReturnCode);
		} else {
			return new MonitoredProcessState(true, false, mReturnCode);
		}
	}

	/**
	 * Wait and block for some time for the normal termination of the process.
	 * 
	 * @param millis
	 *            The time to wait in milliseconds.
	 * @return A {@link MonitoredProcessState} instance indicating whether the
	 *         process is still running or not and if not, what the return code
	 *         is
	 * @throws InterruptedException
	 */
	public MonitoredProcessState waitfor(long millis) throws InterruptedException {
		if (mMonitor.getState().equals(State.TERMINATED)) {
			return new MonitoredProcessState(false, false, mReturnCode);
		}
		mMonitor.join(millis);
		if (mMonitor.getState().equals(State.TERMINATED)) {
			return new MonitoredProcessState(false, false, mReturnCode);
		} else {
			return new MonitoredProcessState(true, false, mReturnCode);
		}
	}

	/**
	 * Wait and block for some time for the normal termination of the process.
	 * If it did not occur, terminate the process abnormally.
	 * 
	 * @param millis
	 *            The time in milliseconds for which the method waits for the
	 *            normal termination of the process. Must be non-negative. A
	 *            value of 0 means waiting forever.
	 * @return A {@link MonitoredProcessState} instance containing the return
	 *         code of the process or -1
	 */
	public MonitoredProcessState impatientWaitUntilTime(long millis) {
		if (millis < 0) {
			throw new IllegalArgumentException("millis has to be non-negative but was " + millis);
		}
		mLogger.info(String.format("Waiting %s ms for monitored process %s with %s", millis, mID, mCommand));
		MonitoredProcessState mps = null;
		try {
			mps = waitfor(millis);
		} catch (InterruptedException e) {
		}
		if (mps == null || mps.isRunning()) {
			mLogger.warn(String.format("Timeout reached for monitored process %s with %s, terminating...", mID,
					mCommand));
			forceShutdown();
			return new MonitoredProcessState(!mMonitor.getState().equals(State.TERMINATED), true, mReturnCode);
		}
		return mps;
	}

	/**
	 * Wait until the toolchain is cancelled for the termination of the process.
	 * If it did not occur, terminate the process abnormally.
	 * 
	 * @param gracePeriod
	 *            A time period in milliseconds that this method will wait after
	 *            a toolchain cancellation request was received before
	 *            terminating the process. Must be non-negative. 0 means no
	 *            grace-period.
	 * @return A {@link MonitoredProcessState} instance containing the return
	 *         code of the process or -1
	 */
	public MonitoredProcessState impatientWaitUntilToolchainTimeout(long gracePeriod) {
		if (gracePeriod < 0) {
			throw new IllegalArgumentException("gracePeriod must be non-negative");
		}
		mLogger.info(String.format("Waiting until toolchain timeout for monitored process %s with %s", mID, mCommand));
		while (mServices.getProgressMonitorService().continueProcessing()) {
			try {
				MonitoredProcessState state = waitfor(500);
				if (!state.isRunning()) {
					return state;
				}
			} catch (InterruptedException e) {
				break;
			}
		}

		try {
			MonitoredProcessState state = waitfor(gracePeriod);
			if (!state.isRunning()) {
				return state;
			}
		} catch (InterruptedException e) {
		}

		mLogger.warn(String.format(
				"Toolchain was canceled while waiting for monitored process %s with %s, terminating...", mID, mCommand));
		forceShutdown();
		return new MonitoredProcessState(!mMonitor.getState().equals(State.TERMINATED), true, mReturnCode);
	}

	/**
	 * Start a timeout for this process. After the set time is over, the process
	 * will be terminated forcefully. This method is non-blocking. You may only
	 * call this method once!
	 * 
	 * @param millis
	 *            A time period in milliseconds after which the process should
	 *            terminate. Must be larger than zero.
	 */
	public synchronized void setCountdownToTermination(final long millis) {
		if (mTimeoutAttached.getAndSet(true)) {
			throw new ConcurrentModificationException("You tried to attach a timeout twice for the monitored process"
					+ mID);
		}

		if (millis <= 0) {
			throw new IllegalArgumentException("millis must be larger than zero");
		}

		new Thread(new Runnable() {

			@Override
			public void run() {
				impatientWaitUntilTime(millis);
			}
		}, "CountdownTimeout watcher for " + mID).start();
	}

	/**
	 * Calling this method will force the process to terminate if the toolchain
	 * terminates, possibly after a grace period. This method is non-blocking.
	 * You may only call this method once!
	 * 
	 * @param gracePeriod
	 *            A time period in milliseconds that we will wait after a
	 *            toolchain cancellation request was received before terminating
	 *            the process. Must be non-negative. 0 means no grace-period.
	 */
	public synchronized void setTerminationAfterToolchainTimeout(final long gracePeriod) {
		if (mTimeoutAttached.getAndSet(true)) {
			throw new ConcurrentModificationException("You tried to attach a timeout twice for the monitored process"
					+ mID);
		}

		if (gracePeriod < 0) {
			throw new IllegalArgumentException("millis must be non-negative");
		}

		new Thread(new Runnable() {

			@Override
			public void run() {
				impatientWaitUntilToolchainTimeout(gracePeriod);
			}
		}, "ToolchainTimeout watcher for " + mID).start();
	}

	/**
	 * Force the process to terminate regardless of its state. Will first try to
	 * use the defined exit command if there is any.
	 */
	public synchronized void forceShutdown() {
		if (isRunning()) {
			if (mExitCommand != null) {
				OutputStream std = mProcess.getOutputStream();
				OutputStreamWriter sw = new OutputStreamWriter(std);
				try {
					sw.write(mExitCommand);
					sw.close();
				} catch (IOException e) {
					mLogger.error("The process started with " + mCommand + " did not receive the exit command "
							+ mExitCommand, e);
				}
				try {
					mLogger.debug("About to join with the monitor thread... ");
					mMonitor.join(200);
					mLogger.debug("Successfully joined ");

				} catch (InterruptedException e) {
					// not necessary to do anything here
					mLogger.debug("Interrupted during join ");
				}
				if (!isRunning()) {
					return;
				}
			}
			mLogger.warn("Forcibly destroying the process started with " + mCommand);
			try {
				mProcess.destroy();
				mProcess.getErrorStream().close();
				mProcess.getInputStream().close();
				mProcess.getOutputStream().close();
			} catch (NullPointerException ex) {
				mLogger.warn("Rare case: The thread was killed right after we checked if it "
						+ "was killed and before we wanted to kill it manually");
			} catch (Exception ex) {
				mLogger.fatal(String.format("Something unexpected happened: %s%n%s", ex,
						ExceptionUtils.getStackTrace(ex)));

			}

			try {
				mStdInStreamPipe.close();
			} catch (IOException e) {
				mLogger.warn("An error occured during closing a pipe", e);
			}

			try {
				mStdErrStreamPipe.close();
			} catch (IOException e) {
				mLogger.warn("An error occured during closing a pipe", e);
			}
		}
		return;
	}

	public OutputStream getOutputStream() {
		return mProcess.getOutputStream();
	}

	public InputStream getErrorStream() {
		return mStdErrStreamPipe;
	}

	public InputStream getInputStream() {
		return mStdInStreamPipe;
	}

	@Override
	public void destroy() {
		forceShutdown();
	}

	@Override
	protected void finalize() throws Throwable {
		forceShutdown();
		super.finalize();
	}

	private ProcessRunner createProcessRunner() {
		return new ProcessRunner(this);
	}

	private static String getKey(int id, String command) {
		return id + " " + command;
	}

	private boolean isRunning() {
		return !mProcessCompleted;
	}

	/**
	 * 
	 * @author dietsch@informatik.uni-freiburg.de
	 * 
	 */
	public class MonitoredProcessState {
		private final boolean mIsRunning;
		private final int mReturnCode;
		private final boolean mIsKilled;

		public MonitoredProcessState(boolean isRunning, boolean isKilled, int returnCode) {
			mIsRunning = isRunning;
			mReturnCode = returnCode;
			mIsKilled = isKilled;
		}

		public boolean isRunning() {
			return mIsRunning;
		}

		public boolean isKilled() {
			return mIsKilled;
		}

		public int getReturnCode() {
			return mReturnCode;
		}
	}

	/**
	 * 
	 * @author dietsch@informatik.uni-freiburg.de
	 * 
	 */
	private class ProcessRunner implements Runnable {

		private final MonitoredProcess mMonitoredProcess;

		private ProcessRunner(MonitoredProcess mp) {
			mMonitoredProcess = mp;
		}

		@Override
		public void run() {
			final Semaphore endOfPumps = new Semaphore(2);
			try {
				PipedOutputStream stdInBufferPipe = new PipedOutputStream(mStdInStreamPipe);
				PipedOutputStream stdErrBufferPipe = new PipedOutputStream(mStdErrStreamPipe);
				setUpStreamBuffer(mMonitoredProcess.mProcess.getInputStream(), stdInBufferPipe, endOfPumps);
				setUpStreamBuffer(mMonitoredProcess.mProcess.getErrorStream(), stdErrBufferPipe, endOfPumps);

			} catch (IOException e) {
				mMonitoredProcess.mLogger.error("The process started with " + mMonitoredProcess.mCommand
						+ " failed during stream data buffering. It will terminate abnormally.", e);
				mMonitoredProcess.mProcess.destroy();
				mMonitoredProcess.mProcess = null;
				mMonitoredProcess.mStorage.removeStorable(getKey(mMonitoredProcess.mID, mMonitoredProcess.mCommand));

				// release enough permits for exec to guarantee return
				mWaitForSetup.release(3);
				return;
			}

			try {
				mWaitForSetup.release();
				mMonitoredProcess.mReturnCode = mMonitoredProcess.mProcess.waitFor();
				mMonitoredProcess.mLogger.debug("Finished waiting for process!");
				endOfPumps.acquireUninterruptibly(2);
				mMonitoredProcess.mLogger.debug("Finished waiting for pump threads!");
				mMonitoredProcess.mProcessCompleted = true;
			} catch (InterruptedException e) {
				mMonitoredProcess.mLogger.error("The process started with " + mMonitoredProcess.mCommand
						+ " was interrupted. It will terminate abnormally.", e);
			} finally {
				mMonitoredProcess.mProcess.destroy();
				mMonitoredProcess.mProcess = null;
				mMonitoredProcess.mStorage.removeStorable(getKey(mMonitoredProcess.mID, mMonitoredProcess.mCommand));
			}
		}

		private void setUpStreamBuffer(final InputStream is, final OutputStream os, final Semaphore endOfPumps) {

			endOfPumps.acquireUninterruptibly();
			final InputStreamReader streamReader = new InputStreamReader(is);
			final String threadName = "MonitoredProcess " + mID + " StreamBuffer";
			new Thread(new Runnable() {
				public void run() {

					BufferedReader br = new BufferedReader(streamReader);
					int chunk = -1;
					mWaitForSetup.release();
					try {
						while ((chunk = br.read()) != -1) {
							os.write(chunk);
							os.flush();
						}
					} catch (IOException e) {
						mMonitoredProcess.mLogger.warn("The stream was forcibly closed (" + mMonitoredProcess.mCommand
								+ ")");
					} finally {
						try {
							br.close();
							os.flush();
							os.close();
						} catch (IOException e) {
							mMonitoredProcess.mLogger.fatal("During closing of the streams, an error occured ("
									+ mMonitoredProcess.mCommand + ")");
						}
						endOfPumps.release();
					}
				}
			}, threadName).start();
		}

	}
}
