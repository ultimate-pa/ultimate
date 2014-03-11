/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.ep.interfaces;

import org.apache.log4j.Appender;

/**
 * Interface for Plugins defining a LoggingWindow.
 * @author dietsch
 *
 * CO: extended with appender .. seems to be more compfortable
 * and we can then use it with log4j
 */
public interface ILoggingWindow extends Appender, IInitializableUltimatePlugin {

	/**
	 * Method for writing string on window. 
	 * @param s String which should be written on window.
	 */
	void write(String s);
	
	/**
	 * Clears window.
	 */
	void clear();
}
