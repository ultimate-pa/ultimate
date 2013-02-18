/*
 * Project:	CoreRCP
 * Package:	de.uni_freiburg.informatik.ultimate.model.repository
 * File:	PersistentObjectFoundException.java created on Oct 28, 2009 by Björn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.model.repository;


/**
 * PersistentObjectFoundException
 *
 * @author Björn Buchhold
 *
 */
public class PersistentObjectNotFoundException extends DataAccessException {

	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = 3503439079052656989L;
	
	/**
	 * @param msg
	 */
	public PersistentObjectNotFoundException(String msg){
		super(msg);
	}
	
	/**
	 * @param msg
	 * @param cause
	 */
	public PersistentObjectNotFoundException(String msg, Throwable cause){
		super(msg, cause);
	}

	/**
	 * @param e
	 */
	public PersistentObjectNotFoundException(Throwable e) {
		super("An error occurred because the object could not be found properly!",e);
	}
}
