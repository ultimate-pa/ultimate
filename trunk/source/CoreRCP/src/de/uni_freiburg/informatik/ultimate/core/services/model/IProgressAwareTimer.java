package de.uni_freiburg.informatik.ultimate.core.services.model;

/**
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
	 */
	public IProgressAwareTimer getChildTimer(long timeout);
}
