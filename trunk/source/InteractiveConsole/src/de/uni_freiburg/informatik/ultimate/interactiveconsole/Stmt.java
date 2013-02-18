package de.uni_freiburg.informatik.ultimate.interactiveconsole;

/**
 * Mother class for all interactive console statements.
 * 
 * @author Christian Simon
 *
 */
abstract class Stmt {
	
	protected InteractiveConsoleController controller;
	
	/**
	 * All child classes must implement this method. It will
	 * be called once a command-line input has been parsed.
	 */
	public abstract void execute();
	
	
	/**
	 * The statements will have to access certain information
	 * from their controller. So this will be called after 
	 * parsing and before calling execute().
	 * 
	 * @param contr
	 */
	public void setController(InteractiveConsoleController contr) {
		this.controller = contr;
	}
}

