package de.uni_freiburg.informatik.ultimate.core.services;

public interface IProgressMonitorService {

	/**
	 * Return false iff cancellation of Toolchain is requested or deadline is
	 * exceeded.
	 */
	public boolean continueProcessing();

	public void setSubtask(String task);

	/**
	 * Set a time limit after which the toolchain should be stopped.
	 * 
	 * A convenient way of setting this deadline is using
	 * System.currentTimeMillis() + timelimit (in ms) as value right before
	 * calling start(...).
	 * 
	 * @param date
	 *            A date in the future (aka, the difference, measured in
	 *            milliseconds, between the current time and midnight, January
	 *            1, 1970 UTC) after which a running toolchain should be
	 *            stopped.
	 */
	public void setDeadline(long date);

	public void cancelToolchain();

}