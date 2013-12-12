/**
 * Thats what Codan needs as a List from Ultimate.
 */
package de.uni_freiburg.informatik.ultimate.result;

import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * Result produced by a plugin of ULTIMATE and visualized by a frontend of 
 * ULTIMATE.
 * @author Markus Lindenmann
 * @author Stefan Wissert
 * @author Oleksii Saukh
 * @author heizmann@informatik.uni-freiburg.de
 * @date 02.01.2012
 */
public interface IResult {
	/**
	 * Location of the input to which this result is related.
	 */
	public ILocation getLocation();
	
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
