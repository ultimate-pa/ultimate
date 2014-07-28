/*
 * Project:	CoreRCP
 * Package:	de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain
 * File:	IStorable.java created on Mar 8, 2010 by Björn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.core.services;

/**
 * {@link IStorable} should be implemented by all services or storables that are
 * distributed through {@link IToolchainStorage}.
 * 
 * @author dietsch
 * 
 */
public interface IStorable {

	/**
	 * Method to destroy the external tool and free the occupied memory.
	 */
	void destroy();
}
