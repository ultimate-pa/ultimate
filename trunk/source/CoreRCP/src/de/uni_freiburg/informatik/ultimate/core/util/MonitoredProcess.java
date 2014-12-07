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
import java.util.concurrent.Semaphore;
import java.util.concurrent.atomic.AtomicInteger;

import org.apache.commons.lang3.StringUtils;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.IStorable;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.ExceptionUtils;

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

		// wait until all 3 threads are ready (stderr buffer, stdinbuffer,
		// actual process watcher) before returning from exec
		mWaitForSetup = new Semaphore(-2);
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

	private void start(String workingDir, IToolchainStorage storage, String oneLineCmd) {
		mID = sInstanceCounter.incrementAndGet();
		storage.putStorable(getKey(mID, oneLineCmd), this);

		mMonitor = new Thread(createProcessRunner(), "MonitoredProcess " + mID + " " + oneLineCmd);
		mLogger.info(String.format("Starting monitored process with %s (exit command is %s, workingDir is %s)",
				mCommand, mExitCommand, workingDir));
		mMonitor.start();
		mWaitForSetup.acquireUninterruptibly();
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

	public static MonitoredProcess exec(String command, IUltimateServiceProvider services, IToolchainStorage storage)
			throws IOException {
		return exec(command, null, services, storage);
	}

	public MonitoredProcessState waitfor() throws InterruptedException {
		if (mMonitor.getState().equals(State.TERMINATED)) {
			return new MonitoredProcessState(false, mReturnCode);
		}
		mMonitor.join();
		if (mMonitor.getState().equals(State.TERMINATED)) {
			return new MonitoredProcessState(false, mReturnCode);
		} else {
			return new MonitoredProcessState(true, mReturnCode);
		}
	}

	/**
	 * 
	 * @param millis
	 * @return -1 iff the process is still running, the return code of the
	 *         thread otherwise
	 * @throws InterruptedException
	 */
	public MonitoredProcessState waitfor(long millis) throws InterruptedException {
		if (mMonitor.getState().equals(State.TERMINATED)) {
			return new MonitoredProcessState(false, mReturnCode);
		}
		mMonitor.join(millis);
		if (mMonitor.getState().equals(State.TERMINATED)) {
			return new MonitoredProcessState(false, mReturnCode);
		} else {
			return new MonitoredProcessState(true, mReturnCode);
		}
	}

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

		public MonitoredProcessState(boolean isRunning, int returnCode) {
			mIsRunning = isRunning;
			mReturnCode = returnCode;
		}

		public boolean isRunning() {
			return mIsRunning;
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
