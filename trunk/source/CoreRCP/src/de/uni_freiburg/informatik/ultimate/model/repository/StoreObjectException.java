/*
 * Project:	CoreRCP
 * Package:	de.uni_freiburg.informatik.ultimate.model.repository
 * File:	PersistObjectException.java created on Oct 29, 2009 by Björn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.model.repository;


/**
 * PersistObjectException
 *
 * @author Björn Buchhold
 *
 */
public class StoreObjectException extends DataAccessException {

	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = 7672000550303730525L;

	/**
	 * @param e
	 */
	public StoreObjectException(Throwable e) {
		super("Failed to persist object", e);	
	}

	/**
	 * @param string
	 * @param e
	 */
	public StoreObjectException(String string, Throwable e) {
		super(string, e);
	}

}
