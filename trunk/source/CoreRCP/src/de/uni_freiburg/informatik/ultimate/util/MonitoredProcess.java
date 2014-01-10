package de.uni_freiburg.informatik.ultimate.util;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.lang.Thread.State;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;

public final class MonitoredProcess {

	private Logger mLogger;
	private String mCommand;
	private String mExitCommand;
	private Thread mMonitor;

	private volatile Process mProcess;
	private volatile boolean mProcessCompleted;
	private volatile int mReturnCode;

	private MonitoredProcess(Process process, String command, String exitCommand) {
		mLogger = UltimateServices.getInstance().getLogger(
				Activator.s_PLUGIN_ID);
		mProcess = process;
		mProcessCompleted = false;
		mCommand = command;
		mExitCommand = exitCommand;
		mReturnCode = -1;
		mMonitor = null;
	}

	public boolean isRunning() {
		assert mProcessCompleted ^ mProcess != null;
		return !mProcessCompleted;
	}

	public int waitfor() throws InterruptedException {
		if (mMonitor.getState().equals(State.TERMINATED)) {
			return mReturnCode;
		}
		mMonitor.join();
		return mReturnCode;
	}

	/**
	 * 
	 * @param command
	 * @return
	 * @throws IOException
	 */
	public static MonitoredProcess exec(String command, String exitCommand)
			throws IOException {
		final MonitoredProcess mp = new MonitoredProcess(Runtime.getRuntime()
				.exec(command), command, exitCommand);

		UltimateServices.getInstance().registerProcess(mp);
		mp.mMonitor = new Thread(new Runnable() {

			@Override
			public void run() {
				try {
					mp.mReturnCode = mp.mProcess.waitFor();
					mp.mLogger.debug("Finished waiting for process!");
					mp.mProcessCompleted = true;
				} catch (InterruptedException e) {
					mp.mLogger.error(
							"The process started with "
									+ mp.mCommand
									+ " was interrupted. It will terminate abnormally.",
							e);
				} finally {
					mp.mProcess.destroy();
					mp.mProcess = null;
					UltimateServices.getInstance().unregisterProcess(mp);
				}
			}
		}, command);
		mp.mLogger.info(String.format(
				"Starting monitored process with %s (exit command is %s)",
				mp.mCommand, mp.mExitCommand));
		mp.mMonitor.start();
		return mp;
	}

	public static MonitoredProcess exec(String command) throws IOException {
		return exec(command, null);
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
					mLogger.error("The process started with " + mCommand
							+ " did not receive the exit command "
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
			mLogger.warn("Forcibly destroying the process started with "
					+ mCommand);
			try {
				mProcess.destroy();
			} catch (NullPointerException ex) {
				mLogger.warn("Rare case: The thread was killed right after we checked if it "
						+ "was killed and before we wanted to kill it manually");
			} catch (Exception ex) {
				mLogger.fatal(String.format(
						"Something unexpected happened: %s%n%s", ex,
						ExceptionUtils.getStackTrace(ex)));

			}
		}
		return;
	}

	public OutputStream getOutputStream() {
		return mProcess.getOutputStream();
	}

	public InputStream getInputStream() {
		return mProcess.getInputStream();
	}

}
