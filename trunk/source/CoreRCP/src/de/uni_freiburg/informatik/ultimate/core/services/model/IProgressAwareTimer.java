package de.uni_freiburg.informatik.ultimate.core.services.model;

/**
 * An object that allows you to create timeouts that trigger either if the
 * parent timeout triggers or when the local timeout triggers.
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface IProgressAwareTimer {

	/**
	 * Return false iff cancellation of Toolchain is requested or deadline is
	 * exceeded.
	 */
	public boolean continueProcessing();

	/**
	 * Create a new timer that will expire after <code>timeout</code>
	 * milliseconds.
	 * 
	 * @param timeout
	 *            A timeout in milliseconds. Has to be larger than 0.
	 * @return A new timer.
	 */
	public IProgressAwareTimer getChildTimer(long timeout);

	/**
	 * Create a new timer that will expire after the specified
	 * <code>percentage</code> of the parent timer has been elapsed.
	 * 
	 * @param percentage
	 *            A value > 0 and <= 1.0
	 * @return A new timer.
	 */
	public IProgressAwareTimer getChildTimer(double percentage);
	
}
