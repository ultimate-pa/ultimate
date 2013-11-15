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
		mExitCommand = null;
		mCommand = command;
		mReturnCode = -1;
		mMonitor = null;
	}

	public boolean isRunning() {
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
					wait(100);
				} catch (InterruptedException e) {
					// not necessary to do anything here
				}
				if (!isRunning()) {
					return;
				}
			}
			mLogger.warn("Forcibly destorying the process started with "
					+ mCommand);
			mProcess.destroy();
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
