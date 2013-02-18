/*
 * Project:	CoreRCP
 * Package:	local.stalin.model.repository
 * File:	DataAccessException.java created on Oct 28, 2009 by Björn Buchhold
 *
 */
package local.stalin.model.repository;

/**
 * DataAccessException
 * Root of the Exception Hierarchy for Data Access.
 * Catching this kind of Exception allows the user to react t data access failure
 * without knowing the particular reason (wrong usage, unavailable data access service etc)
 *
 * @author Björn Buchhold
 *
 */
public class DataAccessException extends Exception {

	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = -481244605773347116L;
	
	/**
	 * @param msg
	 */
	public DataAccessException(String msg){
		super(msg);
	}
	
	/**
	 * @param msg
	 * @param cause
	 */
	public DataAccessException(String msg, Throwable cause){
		super(msg, cause);
	}
}
