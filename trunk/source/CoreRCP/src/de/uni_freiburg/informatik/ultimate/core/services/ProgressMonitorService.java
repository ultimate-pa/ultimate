package de.uni_freiburg.informatik.ultimate.core.services;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.IProgressMonitor;

public class ProgressMonitorService implements IStorable, IToolchainCancel, IProgressMonitorService {

	private static final String sKey = "CancelNotificationService";

	private IProgressMonitor mMonitor;
	private long mDeadline;
	private Logger mLogger;
	private IToolchainCancel mToolchainCancel;
	private boolean mCancelRequest;

	public ProgressMonitorService(IProgressMonitor monitor, long deadline, Logger logger, IToolchainCancel cancel) {
		assert monitor != null;
		mMonitor = monitor;
		mDeadline = deadline;
		mLogger = logger;
		mToolchainCancel = cancel;
		mCancelRequest = false;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.core.services.IProgressMonitorService#continueProcessing()
	 */
	@Override
	public boolean continueProcessing() {
		boolean cancel = mMonitor.isCanceled() || mCancelRequest || System.currentTimeMillis() > mDeadline;
		if (cancel) {
			mLogger.debug("Do not continue processing!");
		}
		return !cancel;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.core.services.IProgressMonitorService#setSubtask(java.lang.String)
	 */
	@Override
	public void setSubtask(String task) {
		mMonitor.subTask(task);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.core.services.IProgressMonitorService#setDeadline(long)
	 */
	@Override
	public void setDeadline(long date) {
		if (System.currentTimeMillis() >= date) {
			mLogger.warn(String
					.format("Deadline was set to a date in the past, " + "effectively stopping the toolchain. "
							+ "Is this what you intended? Value of date was %,d", date));

		}
		mDeadline = date;
	}

	static ProgressMonitorService getService(IToolchainStorage storage) {
		assert storage != null;
		return (ProgressMonitorService) storage.getStorable(sKey);
	}

	public static String getServiceKey() {
		return sKey;
	}

	@Override
	public void destroy() {
		mMonitor.done();
	}

	@Override
	public void cancelToolchain() {
		mToolchainCancel.cancelToolchain();
		mCancelRequest = true;
	}

}
