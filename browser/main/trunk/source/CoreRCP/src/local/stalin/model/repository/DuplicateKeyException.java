/*
 * Project:	CoreRCP
 * Package:	local.stalin.model.repository
 * File:	DuplicateKeyException.java created on Oct 29, 2009 by Björn Buchhold
 *
 */
package local.stalin.model.repository;

/**
 * DuplicateKeyException
 *
 * @author Björn Buchhold
 *
 */
public class DuplicateKeyException extends DataAccessException {
	

	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = -8860449896992867725L;
	
	/**
	 * @param msg
	 */
	public DuplicateKeyException(String msg) {
		super(msg);
	}
	
	/**
	 * @param msg
	 * @param cause
	 */
	public DuplicateKeyException(String msg, Throwable cause) {
		super(msg, cause);
	}

	
}
