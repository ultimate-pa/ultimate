/*
 * Project:	CoreRCP
 * Package:	local.stalin.model.repository
 * File:	InvalidKeyException.java created on Oct 29, 2009 by Björn Buchhold
 *
 */
package local.stalin.model.repository;

import java.io.FileNotFoundException;

/**
 * InvalidKeyException
 *
 * @author Björn Buchhold
 *
 */
public class InvalidKeyException extends StoreObjectException {

	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = 988620680137659382L;

	/**
	 * @param string
	 * @param e
	 */
	public InvalidKeyException(String string, FileNotFoundException e) {
		super(string, e);
	}

}
