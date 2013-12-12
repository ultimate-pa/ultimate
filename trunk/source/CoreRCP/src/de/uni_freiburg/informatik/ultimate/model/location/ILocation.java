/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.model.location;

import de.uni_freiburg.informatik.ultimate.result.Check;

/**
 * Defines an area in a text file.
 * Used to specify where an ASTNode is defined.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public interface ILocation {
	
	/**
	 * @return Name of this {@code Location}s file.
	 */
	public String getFileName();
	
	/**
	 * @return Number of line where this {@code Location} begins.
	 */
	public int getStartLine();
	
	/**
	 * @return Number of line where this {@code Location} ends.
	 */
	public int getEndLine();
	
	/**
	 * @return Number of column where this {@code Location} begins.
	 */
	public int getStartColumn();
	
	/**
	 * @return Number of column where this {@code Location} ends.
	 */
	public int getEndColumn();

	/**
	 * This {@code Location} can be an auxiliary {@code Location} constructed
	 * with respect to some <i>origin</i> {@code Location}. E.g.,
	 * if this is an auxiliary {@code Location} for the else-branch the
	 * <i>origin</i> {@code Location} can be the {@code Location} of an 
	 * if-then-else statement of a program.
	 * 
	 * If this {@code Location} is no auxiliary location the <i>origin</i> is
	 * the location itself.
	 */
	@Deprecated
	public ILocation getOrigin();
	
	
	
	/**
	 * Textual description of the type of specification which is checked here.
	 * E.g., "NullPointerException", "AssertStatement" etc.
	 */
	@Deprecated
	public Check checkedSpecification();
	
	
	
	/**
	 * 
	 * @return true iff this Location represents a loop.
	 */
	@Deprecated
	public boolean isLoop();
}
