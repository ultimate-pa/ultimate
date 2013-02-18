/**
 * 
 */
package local.stalin.model;

import java.io.Serializable;

/**
 * this represents a location of a token, use it to determine the source file,
 * the package ant the line number of a token
 * 
 * Changed for STALIN 2.0
 * Locations now support more than a line number. They are divided in
 * lines and columns and comprise a range of those.
 * 
 * @author justus
 */
public class Location implements Serializable {
	private static final long serialVersionUID = 4495864682359937328L;

	protected int startLine;
	protected int endLine;
	protected int startColumn;
	protected int endColumn;

	protected String m_FileName;
	protected String m_Package;

	/**
	 * default constructor, this defines a no location
	 */
	public Location() {
		m_FileName = "";
		m_Package = "";
		this.startLine = 0;
		this.endLine = 0;
		this.startColumn = 0;
		this.endColumn = 0;
	}

	/**
	 * the preferred constructor, has parameters for location's properties
	 * 
	 */
	public Location(String fileName, String thePackage, int startLine,
			int endLine, int startColum, int endColumn) {
		this.m_FileName = fileName;
		this.m_Package = thePackage;
		this.startLine = startLine;
		this.endLine = endLine;
		this.startColumn = startColum;
		this.endColumn = endColumn;
	}

	/**
	 * Constructs a location with where start and end lineNumber both equal
	 * the param, and start and end column both are set to 1.
	 * 
	 * Use of this constructor is discouraged, since imprecise locations will
	 * be created. It is only present to ensure backwards compatibility to Stalin1.
	 */
	@Deprecated
	public Location(String filename, String thePackage, int lineNr) {
		this(filename, thePackage, lineNr, lineNr, 0, 1);
	}

	public String toString() {
		if (m_Package != null)
			return m_Package + "." + m_FileName + ":" + startLine + "/"
					+ startColumn + "-" + endLine + "/" + endColumn;
		else
			return m_FileName + ":" + startLine + "/" + startColumn + "-"
					+ endLine + "/" + endColumn;
	}

	/**
	 * getter for field startLine
	 * 
	 * @return the startLine
	 */
	public int getStartLine() {
		return this.startLine;
	}

	/**
	 * getter for field endLine
	 * 
	 * @return the endLine
	 */
	public int getEndLine() {
		return this.endLine;
	}

	/**
	 * getter for field startColumn
	 * 
	 * @return the startColumn
	 */
	public int getStartColumn() {
		return this.startColumn;
	}

	/**
	 * getter for field endColumn
	 * 
	 * @return the endColumn
	 */
	public int getEndColumn() {
		return this.endColumn;
	}

	/**
	 * getter for field m_FileName
	 * 
	 * @return the m_FileName
	 */
	public String getFileName() {
		return this.m_FileName;
	}

	/**
	 * setter for field m_FileName
	 * @param mFileName the m_FileName to set
	 */
	public void setFileName(String mFileName) {
		this.m_FileName = mFileName;
	}

	/**
	 * getter for field m_Package
	 * 
	 * @return the m_Package
	 */
	public String getPackage() {
		return this.m_Package;
	}
}
