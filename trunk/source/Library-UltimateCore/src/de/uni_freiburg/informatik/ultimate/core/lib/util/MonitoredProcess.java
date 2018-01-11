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
package de.uni_freiburg.informatik.ultimate.core.lib.util;

import java.io.Closeable;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.lang.Thread.State;
import java.nio.charset.Charset;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.ConcurrentModificationException;
import java.util.List;
import java.util.concurrent.Semaphore;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IStorable;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * A MonitoredProcess is a {@link Process} that will be terminated at the end of the toolchain from which it was
 * created.
 *
 * @author dietsch@informatik.uni-freiburg.de
 */
public final class MonitoredProcess implements IStorable {

	/**
	 * Time in milliseconds to wait for the termination of a process after sending the exit command.
	 */
	private static final int WAIT_FOR_EXIT_COMMAND_MILLIS = 200;

	/**
	 * Time in milliseconds to wait between checks if the toolchain is still running.
	 */
	private static final int WAIT_BETWEEN_CHECKS_MILLIS = 500;

	/**
	 * Buffer size in bytes.
	 */
	private static final int DEFAULT_BUFFER_SIZE = 2048;

	/**
	 * -2 because we wait until all 3 threads (stderr buffer, stdin buffer, actual process watcher) are ready.
	 */
	private static final int INITIAL_SEMAPHORE_COUNT = -2;

	private static final AtomicInteger sInstanceCounter = new AtomicInteger();

	private final ILogger mLogger;
	private final IToolchainStorage mStorage;
	private final IUltimateServiceProvider mServices;
	private final String mCommand;
	private final String mExitCommand;
	private final PipedInputStream mStdInStreamPipe;
	private final PipedInputStream mStdErrStreamPipe;
	private final Semaphore mWaitForSetup;
	private final AtomicBoolean mTimeoutAttached;

	private Thread mMonitor;
	private int mID;

	private volatile Process mProcess;
	private volatile boolean mProcessCompleted;
	private volatile int mReturnCode;

	private MonitoredProcess(final Process process, final String command, final String exitCommand,
			final IUltimateServiceProvider services, final IToolchainStorage storage, final ILogger logger) {
		assert storage != null;
		assert services != null;
		mStorage = storage;
		mServices = services;
		mLogger = logger;
		mProcess = process;
		assert mProcess != null;
		mProcessCompleted = false;
		mCommand = command;
		mExitCommand = exitCommand;
		mReturnCode = -1;
		mMonitor = null;
		mStdInStreamPipe = new PipedInputStream(DEFAULT_BUFFER_SIZE);
		mStdErrStreamPipe = new PipedInputStream(DEFAULT_BUFFER_SIZE);
		mWaitForSetup = new Semaphore(INITIAL_SEMAPHORE_COUNT);
		mTimeoutAttached = new AtomicBoolean(false);
	}

	/**
	 * Start a new monitored process. The process will be terminated at the end of the toolchain. Note that you should
	 * not start an external process through some wrapper script, because Java will have trouble terminating this
	 * processes due to bug <a href="http://bugs.java.com/bugdatabase/view_bug.do?bug_id=4770092">JDK-4770092</a>. If
	 * this occurs, Ultimate may deadlock because it cannot close input and output streams of the unresponsive process
	 * reliably.
	 *
	 * @param command
	 *            A string array containing the command and its possible arguments that will be used to start a new
	 *            process.
	 * @param workingDir
	 *            A string describing the directory path of the working directory that should be used to start the
	 *            process.
	 * @param exitCommand
	 *            A string describing an "exit" command that should be sent to the standard input stream of the running
	 *            process before trying to shut it down.
	 * @param services
	 *            An instance of {@link IUltimateServiceProvider} that should be used to report errors.
	 * @param storage
	 *            An instance of {@link IToolchainStorage} that should be used to register this process for destruction
	 *            after the current toolchain completes.
	 * @return A monitored process instance that represents the started process.
	 * @throws IOException
	 *             If the command cannot be executed because there is no executable, this exception is thrown.
	 */
	public static MonitoredProcess exec(final String[] command, final String workingDir, final String exitCommand,
			final IUltimateServiceProvider services, final IToolchainStorage storage) throws IOException {
		final MonitoredProcess newMonitoredProcess;
		final String oneLineCmd = Arrays.stream(command).reduce((a, b) -> a + " " + b).get();
		final ILogger logger = services.getLoggingService().getControllerLogger();
		if (workingDir == null) {
			if (command.length > 0) {
				File f = new File(command[0]);
				if (f.exists()) {
					command[0] = f.getAbsolutePath();
				} else {
					f = new File(Paths.get(System.getProperty("user.dir"), command[0]).toString());
					if (f.exists() && f.canExecute()) {
						command[0] = f.getAbsolutePath();
					} else {
						final File absolutePath = CoreUtil.findExecutableBinaryOnPath(command[0]);
						if (absolutePath == null) {
							logger.error(
									"Could not determine absolute path of external process, hoping that OS will resolve "
											+ command[0]);
						} else {
							command[0] = absolutePath.getAbsolutePath();
						}
					}
				}
			}
			logger.info("No working directory specified, using " + command[0]);
			newMonitoredProcess = new MonitoredProcess(Runtime.getRuntime().exec(command), oneLineCmd, exitCommand,
					services, storage, logger);
		} else {
			newMonitoredProcess = new MonitoredProcess(Runtime.getRuntime().exec(command, null, new File(workingDir)),
					oneLineCmd, exitCommand, services, storage, logger);
		}

		newMonitoredProcess.start(workingDir, storage, oneLineCmd);
		return newMonitoredProcess;
	}

	/**
	 * Start a new monitored process. The process will be terminated at the end of the toolchain. Note that you should
	 * not start an external process through some wrapper script, because Java will have trouble terminating this
	 * processes due to bug <a href="http://bugs.java.com/bugdatabase/view_bug.do?bug_id=4770092">JDK-4770092</a>. If
	 * this occurs, Ultimate may deadlock because it cannot close input and output streams of the unresponsive process
	 * reliably.
	 *
	 * @param command
	 *            A command without arguments that will be used to start a new process.
	 * @param exitCommand
	 *            A string describing an "exit" command that should be sent to the standard input stream of the running
	 *            process before trying to shut it down.
	 * @param services
	 *            An instance of {@link IUltimateServiceProvider} that should be used to report errors.
	 * @param storage
	 *            An instance of {@link IToolchainStorage} that should be used to register this process for destruction
	 *            after the current toolchain completes.
	 * @return A monitored process instance that represents the started process.
	 * @throws IOException
	 *             If the command cannot be executed because there is no executable, this exception is thrown.
	 */
	public static MonitoredProcess exec(final String command, final String exitCommand,
			final IUltimateServiceProvider services, final IToolchainStorage storage) throws IOException {
		return exec(command.split(" "), null, exitCommand, services, storage);
	}

	private void start(final String workingDir, final IToolchainStorage storage, final String oneLineCmd) {
		mID = sInstanceCounter.incrementAndGet();
		storage.putStorable(getKey(mID, oneLineCmd), this);

		mMonitor = new Thread(new ProcessRunner(this), "MonitoredProcess " + mID + " " + oneLineCmd);
		mLogger.info(String.format("Starting monitored process %s with %s (exit command is %s, workingDir is %s)", mID,
				mCommand, mExitCommand, workingDir));
		mMonitor.start();
		mWaitForSetup.acquireUninterruptibly();
	}

	/**
	 * Wait forever until the {@link MonitoredProcess} terminates.
	 *
	 * @return A {@link MonitoredProcessState} instance indicating whether the process is still running or not and if
	 *         not, what the return code is.
	 * @throws InterruptedException
	 *             If any thread has interrupted the monitor thread. The interrupted status of the monitor thread is
	 *             cleared when this exception is thrown.
	 */
	public MonitoredProcessState waitfor() throws InterruptedException {
		if (mMonitor.getState() == State.TERMINATED) {
			return new MonitoredProcessState(false, false, mReturnCode);
		}
		mMonitor.join();
		if (mMonitor.getState() == State.TERMINATED) {
			return new MonitoredProcessState(false, false, mReturnCode);
		}
		return new MonitoredProcessState(true, false, mReturnCode);
	}

	/**
	 * Wait and block for some time for the normal termination of the process.
	 *
	 * @param millis
	 *            The time to wait in milliseconds.
	 * @return A {@link MonitoredProcessState} instance indicating whether the process is still running or not and if
	 *         not, what the return code is.
	 * @throws InterruptedException
	 *             If any thread has interrupted the monitor thread. The interrupted status of the monitor thread is
	 *             cleared when this exception is thrown.
	 */
	public MonitoredProcessState waitfor(final long millis) throws InterruptedException {
		if (mMonitor.getState() == State.TERMINATED) {
			return new MonitoredProcessState(false, false, mReturnCode);
		}
		mMonitor.join(millis);
		if (mMonitor.getState() == State.TERMINATED) {
			return new MonitoredProcessState(false, false, mReturnCode);
		}
		return new MonitoredProcessState(true, false, mReturnCode);
	}

	/**
	 * Wait and block for some time for the normal termination of the process. If it did not occur, terminate the
	 * process abnormally.
	 *
	 * @param millis
	 *            The time in milliseconds for which the method waits for the normal termination of the process. Must be
	 *            non-negative. A value of 0 means waiting forever.
	 * @return A {@link MonitoredProcessState} instance containing the return code of the process or -1
	 */
	public MonitoredProcessState impatientWaitUntilTime(final long millis) {
		if (millis < 0) {
			throw new IllegalArgumentException("millis has to be non-negative but was " + millis);
		}
		mLogger.info(String.format("Waiting %s ms for monitored process %s with %s", millis, mID, mCommand));
		MonitoredProcessState mps = null;
		try {
			mps = waitfor(millis);
		} catch (final InterruptedException e) {
			// ignore interrupted exceptions; they should never occur in this
			// context anyways.
		}
		if (mps == null || mps.isRunning()) {
			mLogger.warn(
					String.format("Timeout reached for monitored process %s with %s, terminating...", mID, mCommand));
			forceShutdown();
			return new MonitoredProcessState(mMonitor.getState() != State.TERMINATED, true, mReturnCode);
		}
		return mps;
	}

	/**
	 * Wait until the toolchain is cancelled for the termination of the process. If it did not occur, terminate the
	 * process abnormally.
	 *
	 * @param gracePeriod
	 *            A time period in milliseconds that this method will wait after a toolchain cancellation request was
	 *            received before terminating the process. Must be non-negative. 0 means no grace-period.
	 * @return A {@link MonitoredProcessState} instance containing the return code of the process or -1
	 */
	public MonitoredProcessState impatientWaitUntilToolchainTimeout(final long gracePeriod) {
		if (gracePeriod < 0) {
			throw new IllegalArgumentException("gracePeriod must be non-negative");
		}
		mLogger.info(String.format("Waiting until toolchain timeout for monitored process %s with %s", mID, mCommand));
		final IProgressMonitorService progressService = mServices.getProgressMonitorService();
		while (progressService != null && progressService.continueProcessing()) {
			try {
				final MonitoredProcessState state = waitfor(WAIT_BETWEEN_CHECKS_MILLIS);
				if (!state.isRunning()) {
					return state;
				}
			} catch (final InterruptedException e) {
				break;
			}
		}

		try {
			final MonitoredProcessState state = waitfor(gracePeriod);
			if (!state.isRunning()) {
				return state;
			}
		} catch (final InterruptedException e) {
			// ignore interrupted exceptions; they should never occur in this
			// context anyways.
		}

		mLogger.warn(
				String.format("Toolchain was canceled while waiting for monitored process %s with %s, terminating...",
						mID, mCommand));
		forceShutdown();
		return new MonitoredProcessState(mMonitor.getState() != State.TERMINATED, true, mReturnCode);
	}

	/**
	 * Start a timeout for this process. After the set time is over, the process will be terminated forcefully. This
	 * method is non-blocking. You may only call this method once!
	 *
	 * @param millis
	 *            A time period in milliseconds after which the process should terminate. Must be larger than zero.
	 */
	public void setCountdownToTermination(final long millis) {
		synchronized (this) {
			if (mTimeoutAttached.getAndSet(true)) {
				throw new ConcurrentModificationException(
						"You tried to attach a timeout twice for the monitored process" + mID);
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
	}

	/**
	 * Calling this method will force the process to terminate if the toolchain terminates, possibly after a grace
	 * period. This method is non-blocking. You may only call this method once!
	 *
	 * @param gracePeriod
	 *            A time period in milliseconds that we will wait after a toolchain cancellation request was received
	 *            before terminating the process. Must be non-negative. 0 means no grace-period.
	 */
	public void setTerminationAfterToolchainTimeout(final long gracePeriod) {
		synchronized (this) {
			if (mTimeoutAttached.getAndSet(true)) {
				throw new ConcurrentModificationException(
						"You tried to attach a timeout twice for the monitored process" + mID);
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
	}

	/**
	 * Force the process to terminate regardless of its state. Will first try to use the defined exit command if there
	 * is any.
	 */
	public void forceShutdown() {
		synchronized (this) {
			if (!isRunning()) {
				return;
			}
			if (mExitCommand != null) {
				final OutputStream std = mProcess.getOutputStream();
				final OutputStreamWriter stdWriter = new OutputStreamWriter(std, Charset.defaultCharset());
				try {
					stdWriter.write(mExitCommand);
					stdWriter.close();
				} catch (final IOException e) {
					mLogger.error(getLogStringPrefix() + " Exception during sending of exit command " + mExitCommand
							+ ": " + e.getMessage());
				}
				try {
					mLogger.debug(getLogStringPrefix() + " About to join with the monitor thread... ");
					mMonitor.join(WAIT_FOR_EXIT_COMMAND_MILLIS);
					mLogger.debug(getLogStringPrefix() + " Successfully joined");

				} catch (final InterruptedException e) {
					// not necessary to do anything here
					mLogger.debug(getLogStringPrefix() + " Interrupted during join");
				}
				if (!isRunning()) {
					return;
				}
			}
			mLogger.warn(getLogStringPrefix() + " Forcibly destroying the process");
			final List<InputStream> tobeclosed = new ArrayList<>(5);
			try {
				// mProcess.destroyForcibly();
				// mStorage.removeStorable(getKey(mID, mCommand));
				// mProcess.getErrorStream().close();
				// mProcess.getInputStream().close();
				// mProcess.getOutputStream().flush();
				// mProcess.getOutputStream().close();
				// mProcess = null;
				tobeclosed.add(mProcess.getInputStream());
				tobeclosed.add(mProcess.getErrorStream());
				tobeclosed.add(mStdInStreamPipe);
				tobeclosed.add(mStdErrStreamPipe);
				killProcess();
			} catch (final NullPointerException ex) {
				if (mLogger.isWarnEnabled()) {
					mLogger.warn(
							getLogStringPrefix() + " Rare case: The thread was killed right after we checked if it "
									+ "was killed and before we wanted to kill it manually");
				}
			} catch (final Throwable t) {
				mLogger.fatal(String.format(getLogStringPrefix() + " Something unexpected happened: %s%n%s", t,
						CoreUtil.getStackTrace(t)));
			}

			for (final InputStream stream : tobeclosed) {
				close(stream);
			}

			mProcessCompleted = true;
			mLogger.debug(getLogStringPrefix() + " Forcibly destroyed the process");
		}
	}

	private void close(final Closeable pipe) {
		try {
			pipe.close();
		} catch (final IOException e) {
			mLogger.warn(getLogStringPrefix() + " An error occured during closing: " + e.getMessage());
		}
	}

	/**
	 * @return the output stream connected to the normal input of the subprocess. Output to the stream is piped into the
	 *         standard input of the process represented by this Process object.
	 */
	public OutputStream getOutputStream() {
		return mProcess.getOutputStream();
	}

	/**
	 * @return the input stream connected to the error output of the subprocess. The stream obtains data piped from the
	 *         error output of the process represented by this Process object. This stream is already pumped to deal
	 *         with OS buffering.
	 */
	public InputStream getErrorStream() {
		return mStdErrStreamPipe;
	}

	/**
	 * @return the input stream connected to the normal output of the subprocess. The stream obtains data piped from the
	 *         standard output of the process represented by this Process object. This stream is already pumped to deal
	 *         with OS buffering.
	 */
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

	private static String getKey(final int processId, final String command) {
		return processId + " " + command;
	}

	private boolean isRunning() {
		return !mProcessCompleted;
	}

	private String getLogStringPrefix() {
		return "[MP " + mCommand + " (" + mID + ")]";
	}

	private void killProcess() {
		if (mProcess == null) {
			return;
		}
		mProcess.destroyForcibly();
		mProcess = null;
		removeFromStorage();
	}

	private void removeFromStorage() {
		final IStorable storable = mStorage.removeStorable(getKey(mID, mCommand));
		if (storable != null && mLogger.isDebugEnabled()) {
			mLogger.debug(getLogStringPrefix() + " was removed from storage");
		}
	}

	private void logUnreadPipeContent() {
		final String stdout = CoreUtil.convertStreamToString(getInputStream());
		final String stderr = CoreUtil.convertStreamToString(getErrorStream());
		if (stdout.isEmpty() && stderr.isEmpty()) {
			return;
		}

		final StringBuilder sb = new StringBuilder();
		sb.append(getLogStringPrefix()).append(CoreUtil.getPlatformLineSeparator());
		if (!stdout.isEmpty()) {
			sb.append("Unread content of stdout:").append(CoreUtil.getPlatformLineSeparator()).append(stdout);
		}
		if (!stderr.isEmpty()) {
			if (!stdout.isEmpty()) {
				sb.append(CoreUtil.getPlatformLineSeparator());
			}
			sb.append("Unread content of stderr:").append(CoreUtil.getPlatformLineSeparator()).append(stderr);
		}
		mLogger.debug(sb);
	}

	private void setUpStreamBuffer(final InputStream inputStream, final OutputStream outputStream,
			final Semaphore endOfPumps, final String name) {
		endOfPumps.acquireUninterruptibly();
		final InputStreamReader streamReader = new InputStreamReader(inputStream, Charset.defaultCharset());
		final String threadName = "MonitoredProcess " + mID + " StreamBuffer " + name;
		new Thread(new PipePump(outputStream, streamReader, endOfPumps, name), threadName).start();
	}

	/**
	 * @author dietsch@informatik.uni-freiburg.de
	 */
	public static final class MonitoredProcessState {
		private final boolean mIsRunning;
		private final int mReturnCode;
		private final boolean mIsKilled;

		private MonitoredProcessState(final boolean isRunning, final boolean isKilled, final int returnCode) {
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
	 * @author dietsch@informatik.uni-freiburg.de
	 */
	private final class ProcessRunner implements Runnable {

		private final MonitoredProcess mMonitoredProcess;

		private ProcessRunner(final MonitoredProcess monitoredProcess) {
			mMonitoredProcess = monitoredProcess;
		}

		@Override
		public void run() {
			final Semaphore endOfPumps = new Semaphore(-INITIAL_SEMAPHORE_COUNT);
			final PipedOutputStream stdInBufferPipe;
			final PipedOutputStream stdErrBufferPipe;
			try {
				stdInBufferPipe = new PipedOutputStream(mStdInStreamPipe);
				stdErrBufferPipe = new PipedOutputStream(mStdErrStreamPipe);
				setUpStreamBuffer(mMonitoredProcess.mProcess.getInputStream(), stdInBufferPipe, endOfPumps, "stdIn");
				setUpStreamBuffer(mMonitoredProcess.mProcess.getErrorStream(), stdErrBufferPipe, endOfPumps, "stdErr");

			} catch (final IOException e) {
				if (mMonitoredProcess.mLogger.isErrorEnabled()) {
					mMonitoredProcess.mLogger.error(
							getLogStringPrefix() + " Failed during stream data buffering. Terminating abnormally.", e);
				}
				killProcess();
				// release enough permits for exec to guarantee return
				mWaitForSetup.release(1 - INITIAL_SEMAPHORE_COUNT);
				return;
			}

			try {
				mWaitForSetup.release();
				mMonitoredProcess.mReturnCode = mMonitoredProcess.mProcess.waitFor();
				mMonitoredProcess.mLogger.debug(getLogStringPrefix() + " Finished waiting for process!");
				mMonitoredProcess.mProcessCompleted = true;
				if (!endOfPumps.tryAcquire(-INITIAL_SEMAPHORE_COUNT, WAIT_FOR_EXIT_COMMAND_MILLIS,
						TimeUnit.MILLISECONDS)) {
					mMonitoredProcess.mLogger
							.warn(getLogStringPrefix() + " Abandoning pump threads because process wont die!");
				} else {
					mMonitoredProcess.mLogger.debug(getLogStringPrefix() + " Finished waiting for pump threads!");
					if (mMonitoredProcess.mLogger.isDebugEnabled()) {
						logUnreadPipeContent();
					}
				}
			} catch (final InterruptedException e) {
				if (mMonitoredProcess.mLogger.isErrorEnabled()) {
					mMonitoredProcess.mLogger.error(getLogStringPrefix() + " Interrupted. Terminating abnormally.", e);
				}
			} finally {
				killProcess();
			}
		}
	}

	/**
	 * @author dietsch@informatik.uni-freiburg.de
	 */
	private final class PipePump implements Runnable {
		private final OutputStream mOutputStream;
		private final InputStreamReader mStreamReader;
		private final Semaphore mEndOfPumps;
		private final String mPumpName;

		private PipePump(final OutputStream outputStream, final InputStreamReader streamReader,
				final Semaphore endOfPumps, final String pumpName) {
			mOutputStream = outputStream;
			mStreamReader = streamReader;
			mEndOfPumps = endOfPumps;
			mPumpName = pumpName;
		}

		@Override
		public void run() {
			mWaitForSetup.release();
			try {
				int chunk = -1;
				while ((chunk = mStreamReader.read()) != -1) {
					mOutputStream.write(chunk);
					mOutputStream.flush();
				}
			} catch (final IOException /* | InterruptedException */ e) {
				if (mLogger.isWarnEnabled()) {
					mLogger.warn(getLogStringPrefix() + " The stream was forcibly closed: " + mPumpName);
				}
			} finally {
				try {
					mOutputStream.flush();
					mOutputStream.close();
				} catch (final IOException e) {
					mLogger.fatal(getLogStringPrefix() + " During closing of the streams " + mPumpName
							+ ", an error occured");
				}
				mEndOfPumps.release();
			}
		}
	}
}
