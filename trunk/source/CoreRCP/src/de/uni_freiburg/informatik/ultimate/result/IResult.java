package de.uni_freiburg.informatik.ultimate.result;


/**
 * Interface for the results that are produced while running a toolchain.
 * These results are shown by the frontends of ULTIMATE. 
 * @author Markus Lindenmann
 * @author Stefan Wissert
 * @author Oleksii Saukh
 * @author heizmann@informatik.uni-freiburg.de
 * @date 02.01.2012
 */
public interface IResult {
	
	/**
	 * Plugin that derived this IResult.
	 */
	public String getPlugin();
	
	/**
	 * Kind of Result, in a few words. E.g., "procedure precondition can be
	 * violated", "ranking function found", "unsupported syntax".
	 */
	public String getShortDescription();
	
	/**
	 * String representation of the result. Contains all information that are
	 * not already given by
	 * <ul>
	 * <li> location, 
	 * <li> short description,
	 * <li> or objects provided by subinterfaces/subclasses
	 * </ul>
	 */
	public String getLongDescription();
}
