/*
 * Project:	CoreRCP
 * Package:	de.uni_freiburg.informatik.ultimate.model.repository
 * File:	PersistentObjectTypeMismatchException.java created on Oct 29, 2009 by Björn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.model.repository;

/**
 * PersistentObjectTypeMismatchException
 *
 * @author Björn Buchhold
 *
 */
public class PersistentObjectTypeMismatchException extends DataAccessException {

	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = 2801380493879228801L;
	
	/**
	 * @param msg
	 */
	public PersistentObjectTypeMismatchException(String msg){
		super(msg);
	}
	
	/**
	 * @param msg
	 * @param cause
	 */
	public PersistentObjectTypeMismatchException(String msg, Throwable cause){
		super(msg, cause);
	}

}
