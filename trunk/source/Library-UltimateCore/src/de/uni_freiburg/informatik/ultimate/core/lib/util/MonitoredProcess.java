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
import java.util.Objects;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Semaphore;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IStorable;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil;

/**
 * A MonitoredProcess is a {@link Process} that will be terminated at the end of the toolchain from which it was created
 * or by a timeout signaled by {@link IProgressMonitorService}.
 *
 * @author dietsch@informatik.uni-freiburg.de
 */
public final class MonitoredProcess implements IStorable, AutoCloseable {

	/**
	 * Time in milliseconds to wait for the termination of a process after sending the exit command.
	 */
	private static final int WAIT_FOR_EXIT_COMMAND_MILLIS = 200;

	/**
	 * Time in milliseconds to wait between checks if a timeout occurred is still running.
	 */
	private static final int WAIT_BETWEEN_CHECKS_MILLIS = 50;

	/**
	 * Buffer size in bytes.
	 */
	private static final int DEFAULT_BUFFER_SIZE = 2048;

	private static final AtomicInteger sInstanceCounter = new AtomicInteger();

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final String mCommand;
	private final String mExitCommand;
	private final PipedInputStream mStdInStreamPipe;
	private final PipedInputStream mStdErrStreamPipe;

	private final AtomicBoolean mTimeoutAttached;

	private Thread mProcessRunner;
	private int mID;

	private Process mProcess;
	private volatile int mReturnCode;

	private final CompletableFuture<Process> mProcessOnExit;

	private final AtomicBoolean mIsKillProcessCalled;

	private MonitoredProcess(final Process process, final String command, final String exitCommand,
			final IUltimateServiceProvider services, final ILogger logger) {
		mServices = Objects.requireNonNull(services);
		mLogger = Objects.requireNonNull(logger);
		mProcess = Objects.requireNonNull(process);
		mProcessOnExit = mProcess.onExit();
		mCommand = command;
		mExitCommand = exitCommand;
		mReturnCode = -1;
		mProcessRunner = null;
		mStdInStreamPipe = new PipedInputStream(DEFAULT_BUFFER_SIZE);
		mStdErrStreamPipe = new PipedInputStream(DEFAULT_BUFFER_SIZE);

		mTimeoutAttached = new AtomicBoolean(false);
		mIsKillProcessCalled = new AtomicBoolean(false);
	}

	/**
	 * Start a new monitored process. The process will be terminated at the end of the toolchain or if
	 * {@link IProgressMonitorService} signals a timeout. Note that you should not start an external process through
	 * some wrapper script, because Java will have trouble terminating this processes due to bug
	 * <a href="http://bugs.java.com/bugdatabase/view_bug.do?bug_id=4770092">JDK-4770092</a>. If this occurs, Ultimate
	 * may deadlock because it cannot close input and output streams of the unresponsive process reliably.
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
	 * @return A monitored process instance that represents the started process.
	 * @throws IOException
	 *             If the command cannot be executed because there is no executable, this exception is thrown.
	 */
	public static MonitoredProcess exec(final String[] command, final String workingDir, final String exitCommand,
			final IUltimateServiceProvider services) throws IOException {
		if (command == null || command.length == 0) {
			throw new IllegalArgumentException("Cannot execute empty argument");
		}
		if (services == null) {
			throw new NullPointerException("services may not be null");
		}
		final ILogger logger = services.getLoggingService().getControllerLogger();
		final File workingDirFile;
		if (workingDir == null) {
			command[0] = findExecutableBinary(command[0], logger);
			workingDirFile = null;
		} else {
			workingDirFile = new File(workingDir);
		}

		final String oneLineCmd = Arrays.stream(command).reduce((a, b) -> a + " " + b).orElseThrow(AssertionError::new);
		final MonitoredProcess newMonitoredProcess = new MonitoredProcess(
				Runtime.getRuntime().exec(command, null, workingDirFile), oneLineCmd, exitCommand, services, logger);
		newMonitoredProcess.start(workingDir, services.getStorage(), oneLineCmd);
		return newMonitoredProcess;
	}

	private static String findExecutableBinary(final String command, final ILogger logger) {
		final String binary;
		File f = new File(command);
		if (f.exists()) {
			binary = f.getAbsolutePath();
		} else {
			f = new File(Paths.get(System.getProperty("user.dir"), command).toString());
			if (f.exists() && f.canExecute()) {
				binary = f.getAbsolutePath();
			} else {
				final File absolutePath = CoreUtil.findExecutableBinaryOnPath(command);
				if (absolutePath == null) {
					logger.error("Could not determine absolute path of external process, hoping that OS will resolve "
							+ command);
					binary = command;
				} else {
					binary = absolutePath.getAbsolutePath();
				}
			}
		}
		logger.info("No working directory specified, using " + binary);
		return binary;
	}

	/**
	 * Start a new monitored process. The process will be terminated at the end of the toolchain or if
	 * {@link IProgressMonitorService} signals a timeout. Note that you should not start an external process through
	 * some wrapper script, because Java will have trouble terminating this processes due to bug
	 * <a href="http://bugs.java.com/bugdatabase/view_bug.do?bug_id=4770092">JDK-4770092</a>. If this occurs, Ultimate
	 * may deadlock because it cannot close input and output streams of the unresponsive process reliably.
	 *
	 * @param command
	 *            A command without arguments that will be used to start a new process.
	 * @param exitCommand
	 *            A string describing an "exit" command that should be sent to the standard input stream of the running
	 *            process before trying to shut it down.
	 * @param services
	 *            An instance of {@link IUltimateServiceProvider} that is used to report errors, to register this
	 *            process for destruction after the current toolchain completes, and to obtain
	 *            {@link IProgressMonitorService}.
	 * @return A monitored process instance that represents the started process.
	 * @throws IOException
	 *             If the command cannot be executed because there is no executable, this exception is thrown.
	 */
	public static MonitoredProcess exec(final String command, final String exitCommand,
			final IUltimateServiceProvider services) throws IOException {
		return exec(command.split(" "), null, exitCommand, services);
	}

	private void start(final String workingDir, final IToolchainStorage storage, final String oneLineCmd) {
		mID = sInstanceCounter.incrementAndGet();
		final String key = getKey(mID, oneLineCmd);
		final IStorable old = storage.putStorable(key, this);
		if (old != null) {
			mLogger.warn("Destroyed unexpected old storable " + key);
			old.destroy();
		}

		final ProcessRunner pr = new ProcessRunner(this);
		mProcessRunner = new Thread(pr, String.format("MonitoredProcess %s %s", mID, oneLineCmd));
		mLogger.info("Starting monitored process %s with %s (exit command is %s, workingDir is %s)", mID, mCommand,
				mExitCommand, workingDir);
		mProcessRunner.start();
		pr.mEndOfSetup.acquireUninterruptibly();
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
		if (mProcessRunner.getState() == State.TERMINATED) {
			return new MonitoredProcessState(false, false, mReturnCode);
		}
		mProcessRunner.join();
		if (mProcessRunner.getState() == State.TERMINATED) {
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
		if (mProcessRunner.getState() == State.TERMINATED) {
			return new MonitoredProcessState(false, false, mReturnCode);
		}
		mProcessRunner.join(millis);
		if (mProcessRunner.getState() == State.TERMINATED) {
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
		mLogger.info("%s Waiting %s ms for monitored process", getLogStringPrefix(), millis);
		MonitoredProcessState mps = null;
		try {
			mps = waitfor(millis);
		} catch (final InterruptedException e) {
			// ignore interrupted exceptions; they should never occur in this
			// context anyways.
			Thread.currentThread().interrupt();
		}
		if (mps == null || mps.isRunning()) {
			mLogger.warn("%s Timeout reached", getLogStringPrefix());
			forceShutdown();
			try {
				mProcessRunner.join(WAIT_FOR_EXIT_COMMAND_MILLIS);
			} catch (final InterruptedException e) {
				Thread.currentThread().interrupt();
			}
			return new MonitoredProcessState(mProcessRunner.getState() != State.TERMINATED, true, mReturnCode);
		}
		return mps;
	}

	/**
	 * Wait until the toolchain is cancelled or {@link IProgressMonitorService} signals timeout for the termination of
	 * the process. If the process is still running, try sending an exit command if present. If it is still running,
	 * terminate it abnormally.
	 *
	 * @param gracePeriod
	 *            A time period in milliseconds that this method will wait after the toolchain was cancelled or
	 *            {@link IProgressMonitorService} signaled timeout before terminating the process. Must be non-negative.
	 *            0 means no grace-period.
	 * @return A {@link MonitoredProcessState} instance containing the return code of the process or -1
	 */
	public MonitoredProcessState impatientWaitUntilTimeout(final long gracePeriod) {
		if (gracePeriod < 0) {
			throw new IllegalArgumentException("gracePeriod must be non-negative");
		}
		mLogger.info("%s Waiting until timeout for monitored process", getLogStringPrefix());
		final IProgressMonitorService progressService = mServices.getProgressMonitorService();
		while (progressService != null && progressService.continueProcessing()) {
			try {
				final MonitoredProcessState state = waitfor(WAIT_BETWEEN_CHECKS_MILLIS);
				if (!state.isRunning()) {
					return state;
				}
			} catch (final InterruptedException e) {
				Thread.currentThread().interrupt();
				break;
			}
		}
		mLogger.warn("%s Timeout while monitored process is still running, waiting %s ms for graceful end",
				getLogStringPrefix(), gracePeriod);
		try {
			final MonitoredProcessState state = waitfor(gracePeriod);
			if (!state.isRunning()) {
				return state;
			}
		} catch (final InterruptedException e) {
			// ignore interrupted exceptions; they should never occur in this
			// context anyways.
			Thread.currentThread().interrupt();
		}

		forceShutdown();
		return new MonitoredProcessState(mProcessRunner.getState() != State.TERMINATED, true, mReturnCode);
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

			new Thread(() -> impatientWaitUntilTime(millis), "CountdownTimeout watcher for " + mID).start();
		}
	}

	/**
	 * Calling this method will force the process to terminate if the toolchain terminates or
	 * {@link IProgressMonitorService} signals timeout, possibly after a grace period. This method is non-blocking. You
	 * may only call this method once!
	 *
	 * @param gracePeriod
	 *            A time period in milliseconds that we will wait before terminating the process. Must be non-negative.
	 *            0 means no grace-period.
	 */
	public void setTerminationAfterTimeout(final long gracePeriod) {
		synchronized (this) {
			if (mTimeoutAttached.getAndSet(true)) {
				throw new ConcurrentModificationException(
						"You tried to attach a timeout twice for the monitored process" + mID);
			}

			if (gracePeriod < 0) {
				throw new IllegalArgumentException("millis must be non-negative");
			}

			new Thread(() -> impatientWaitUntilTimeout(gracePeriod), "TimeoutWatcher for " + mID).start();
		}
	}

	/**
	 * Force the process to terminate regardless of its state. Will first try to use the defined exit command if there
	 * is any.
	 */
	public void forceShutdown() {
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
				mLogger.error("%s Exception during sending of exit command %s: %s", getLogStringPrefix(), mExitCommand,
						e.getMessage());
			}
			try {
				mLogger.debug("%s About to join with the monitor thread... ", getLogStringPrefix());
				mProcessRunner.join(WAIT_FOR_EXIT_COMMAND_MILLIS);
				mLogger.debug("%s Successfully joined", getLogStringPrefix());

			} catch (final InterruptedException e) {
				// not necessary to do anything here
				mLogger.debug("%s Interrupted during join", getLogStringPrefix());
				Thread.currentThread().interrupt();
			}
			if (!isRunning()) {
				return;
			}
		}
		mLogger.warn("%s Forcibly destroying the process", getLogStringPrefix());
		final List<InputStream> tobeclosed = new ArrayList<>(5);
		try {
			tobeclosed.add(mProcess.getInputStream());
			tobeclosed.add(mProcess.getErrorStream());
			tobeclosed.add(mStdInStreamPipe);
			tobeclosed.add(mStdErrStreamPipe);
			killProcess();
		} catch (final NullPointerException ex) {
			if (mLogger.isWarnEnabled()) {
				mLogger.warn("%s Process already dead, possible race condition", getLogStringPrefix());
			}
		} catch (final Exception ex) {
			mLogger.fatal("%s Something unexpected happened: %s%n%s", getLogStringPrefix(), ex,
					CoreUtil.getStackTrace(ex));
			throw ex;
		}

		for (final InputStream stream : tobeclosed) {
			close(stream);
		}

		mLogger.debug("%s Forcibly destroyed the process", getLogStringPrefix());
	}

	private void close(final Closeable pipe) {
		try {
			pipe.close();
		} catch (final IOException e) {
			mLogger.warn("%s An error occured during closing: %s", getLogStringPrefix(), e.getMessage());
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

	@Override
	public void close() throws Exception {
		forceShutdown();
	}

	private static String getKey(final int processId, final String command) {
		return processId + " " + command;
	}

	public boolean isRunning() {
		return !mProcessOnExit.isDone();
	}

	private String getLogStringPrefix() {
		return "[MP " + mCommand + " (" + mID + ")]";
	}

	/**
	 * Kills the process using {@link Process#destroyForcibly()} and removes it from storage.
	 */
	private void killProcess() {
		// only execute this method once
		if (mIsKillProcessCalled.getAndSet(true)) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("%s Called by %s, but is already killed", getLogStringPrefix(),
						ReflectionUtil.getCallerSignature(3));
			}
			return;
		}

		if (isRunning()) {
			try {
				mProcess.destroyForcibly();
				mProcessOnExit.get(WAIT_FOR_EXIT_COMMAND_MILLIS, TimeUnit.MILLISECONDS);
				mReturnCode = mProcess.exitValue();
				mLogger.info("%s Forceful destruction successful, exit code %d", getLogStringPrefix(), mReturnCode);
			} catch (final InterruptedException e) {
				mLogger.fatal("%s Interrupted while destroying process, abandoning it", getLogStringPrefix());
				Thread.currentThread().interrupt();
			} catch (final ExecutionException e) {
				mLogger.fatal("%s Encounted %s destroying process, abandoning process. Exception: %s",
						getLogStringPrefix(), e.getClass().getSimpleName(), e);
			} catch (final TimeoutException e) {
				mLogger.fatal("%s Could not destroy process within %s ms, abandoning it", getLogStringPrefix(),
						WAIT_FOR_EXIT_COMMAND_MILLIS);
			}
		} else {
			mLogger.info("%s Ended with exit code %s", getLogStringPrefix(), mProcess.exitValue());
			mReturnCode = mProcess.exitValue();
		}
		mProcess = null;
		removeFromStorage();
	}

	private void removeFromStorage() {
		final IStorable storable = mServices.getStorage().removeStorable(getKey(mID, mCommand));
		if (storable != null && mLogger.isDebugEnabled()) {
			mLogger.debug(getLogStringPrefix() + " Removed from storage");
		}
	}

	@Override
	public String toString() {
		if (mExitCommand != null) {
			return String.format("MP %s (%s) with exit command %s", mCommand, mID, mExitCommand);
		}
		return String.format("MP %s (%s) without exit command", mCommand, mID);
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

		/**
		 * -2 because we wait until all 3 threads (stderr buffer, stdin buffer, actual process watcher) are ready.
		 */
		private static final int INITIAL_SEMAPHORE_COUNT = -2;

		private final Semaphore mEndOfSetup;
		private final MonitoredProcess mMonitoredProcess;

		private ProcessRunner(final MonitoredProcess monitoredProcess) {
			mMonitoredProcess = monitoredProcess;
			mEndOfSetup = new Semaphore(INITIAL_SEMAPHORE_COUNT);
		}

		@Override
		public void run() {
			final Semaphore endOfPumps = new Semaphore(-INITIAL_SEMAPHORE_COUNT);
			final PipedOutputStream stdInBufferPipe;
			final PipedOutputStream stdErrBufferPipe;
			final ILogger logger = mMonitoredProcess.mLogger;
			try {
				stdInBufferPipe = new PipedOutputStream(mStdInStreamPipe);
				stdErrBufferPipe = new PipedOutputStream(mStdErrStreamPipe);
				setUpStreamBuffer(mMonitoredProcess.mProcess.getInputStream(), stdInBufferPipe, endOfPumps, "stdIn");
				setUpStreamBuffer(mMonitoredProcess.mProcess.getErrorStream(), stdErrBufferPipe, endOfPumps, "stdErr");

			} catch (final IOException e) {
				if (logger.isErrorEnabled()) {
					logger.error(getLogStringPrefix() + " Failed during stream data buffering. Terminating abnormally.",
							e);
				}
				killProcess();
				// release enough permits for exec to guarantee return
				mEndOfSetup.release(1 - INITIAL_SEMAPHORE_COUNT);
				return;
			}

			try {
				mEndOfSetup.release();
				logger.debug(getLogStringPrefix() + " Finished thread setup");
				mMonitoredProcess.mReturnCode = mMonitoredProcess.mProcess.waitFor();
				logger.debug(getLogStringPrefix() + " Finished waiting for process");
				if (!endOfPumps.tryAcquire(-INITIAL_SEMAPHORE_COUNT, WAIT_FOR_EXIT_COMMAND_MILLIS,
						TimeUnit.MILLISECONDS)) {
					logger.warn(getLogStringPrefix() + " Abandoning pump threads because process wont die");
				} else if (logger.isDebugEnabled()) {
					logger.debug(getLogStringPrefix() + " Finished waiting for pump threads");
					logUnreadPipeContent();
					logger.debug(getLogStringPrefix() + " Finished dumping unread pipe content");
				}
			} catch (final InterruptedException e) {
				logger.error(getLogStringPrefix() + " Pump interrupted. Terminating abnormally.", e);
				Thread.currentThread().interrupt();
			} finally {
				killProcess();
				logger.debug(getLogStringPrefix() + " Exiting monitor thread");
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
			new Thread(new PipePump(outputStream, streamReader, mEndOfSetup, endOfPumps, name), threadName).start();
		}
	}

	/**
	 * @author dietsch@informatik.uni-freiburg.de
	 */
	private final class PipePump implements Runnable {
		private final OutputStream mOutputStream;
		private final InputStreamReader mStreamReader;
		private final Semaphore mEndOfPumps;
		private final Semaphore mEndOfSetup;
		private final String mPumpName;

		private PipePump(final OutputStream outputStream, final InputStreamReader streamReader,
				final Semaphore endOfSetup, final Semaphore endOfPumps, final String pumpName) {
			mOutputStream = outputStream;
			mStreamReader = streamReader;
			mEndOfPumps = endOfPumps;
			mPumpName = pumpName;
			mEndOfSetup = endOfSetup;
		}

		@Override
		public void run() {
			mEndOfSetup.release();
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
