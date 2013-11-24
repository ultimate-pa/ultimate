package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

/**
 * This class is used to interrupt incremental minimization executions.
 * 
 * @see AMinimizeIncremental
 * @author Christian
 */
public final class Interrupt {
	/**
	 * Internal status:
	 * true <=> terminate
	 */
	private boolean m_terminate;
	
	/**
	 * constructor
	 */
	public Interrupt() {
		m_terminate = false;
	}
	
	/**
	 * @return the internal status
	 */
	public boolean getStatus() {
		return m_terminate;
	}
	
	/**
	 * Sets the status to <code>true</code>.
	 */
	public void setStatus() {
		m_terminate = true;
	}
}
