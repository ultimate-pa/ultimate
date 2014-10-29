package de.uni_freiburg.informatik.ultimate.core.util;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.lang.Thread.State;
import java.util.concurrent.atomic.AtomicInteger;

import org.apache.commons.lang3.StringUtils;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.IStorable;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.ExceptionUtils;

public final class MonitoredProcess implements IStorable {

	private Logger mLogger;
	private String mCommand;
	private String mExitCommand;
	private Thread mMonitor;

	private volatile Process mProcess;
	private volatile boolean mProcessCompleted;
	private volatile int mReturnCode;
	private final IToolchainStorage mStorage;
	private static AtomicInteger sInstanceCounter = new AtomicInteger();
	private int mID;
	private IUltimateServiceProvider mServices;

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
	}

	private boolean isRunning() {
		return !mProcessCompleted;
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

		mp.mID = sInstanceCounter.incrementAndGet();
		storage.putStorable(getKey(mp.mID, oneLineCmd), mp);

		mp.mMonitor = new Thread(mp.createProcessRunner(), oneLineCmd);
		mp.mLogger.info(String.format("Starting monitored process with %s (exit command is %s, workingDir is %s)",
				mp.mCommand, mp.mExitCommand, workingDir));
		mp.mMonitor.start();
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
		final MonitoredProcess mp;
		String oneLineCmd = StringUtils.join(command, " ");
		mp = new MonitoredProcess(Runtime.getRuntime().exec(command), oneLineCmd, exitCommand, services, storage);

		mp.mID = sInstanceCounter.incrementAndGet();
		storage.putStorable(getKey(mp.mID, oneLineCmd), mp);

		mp.mMonitor = new Thread(mp.createProcessRunner(), oneLineCmd);
		mp.mLogger.info(String.format("Starting monitored process with %s (exit command is %s)", mp.mCommand,
				mp.mExitCommand));
		mp.mMonitor.start();
		return mp;
	}

	public static MonitoredProcess exec(String command, IUltimateServiceProvider services, IToolchainStorage storage)
			throws IOException {
		return exec(command, null, services, storage);
	}

	private static String getKey(int id, String command) {
		return id + " " + command;
	}

	public void forceShutdown() {
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
			} catch (NullPointerException ex) {
				mLogger.warn("Rare case: The thread was killed right after we checked if it "
						+ "was killed and before we wanted to kill it manually");
			} catch (Exception ex) {
				mLogger.fatal(String.format("Something unexpected happened: %s%n%s", ex,
						ExceptionUtils.getStackTrace(ex)));

			}
		}
		return;
	}

	public OutputStream getOutputStream() {
		return mProcess.getOutputStream();
	}

	public InputStream getErrorStream() {
		return mProcess.getErrorStream();
	}

	public InputStream getInputStream() {
		return mProcess.getInputStream();
	}

	@Override
	protected void finalize() throws Throwable {
		forceShutdown();
		super.finalize();
	}

	private ProcessRunner createProcessRunner() {
		return new ProcessRunner(this);
	}

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

	private class ProcessRunner implements Runnable {

		private MonitoredProcess mMonitoredProcess;

		private ProcessRunner(MonitoredProcess mp) {
			mMonitoredProcess = mp;
		}

		@Override
		public void run() {
			try {
				mMonitoredProcess.mReturnCode = mMonitoredProcess.mProcess.waitFor();

				mMonitoredProcess.mLogger.debug("Finished waiting for process!");
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
	}

	@Override
	public void destroy() {
		forceShutdown();
	}

}
