/*
 * Project:	CoreRCP
 * Package:	de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain
 * File:	IStorable.java created on Mar 8, 2010 by Björn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain;

/**
 * IStorable
 * Interface that should be implemented by external tools that are supposed to be used
 * within Ultimate. A tool-chain may keep several external tools that can be used by the plug-ins.
 * The tool-chain controls the life-cycle of the tools and destroys them when needed.
 * 
 * @author Björn Buchhold, Christian Simon
 * 
 */
public interface IStorable {


	/**
	 * Method to destroy the external tool and free the occupied memory.
	 */
	void destroy();
}
