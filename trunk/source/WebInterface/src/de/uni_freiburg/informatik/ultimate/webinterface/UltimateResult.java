/**
 * Represents an Ultimate Result entry, that can be represented to the client
 * and easily sent via JSON and interpreted with JS. This means i.e. you should
 * avoid complex data structures in this class!
 */
package de.uni_freiburg.informatik.ultimate.webinterface;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 29.03.2011
 */
public class UltimateResult {
	/**
	 * Short description, shown in the annotation.
	 */
	String shortDesc;
	/**
	 * Long description, shown in a table or other listing.
	 */
	String longDesc;
	/**
	 * Start line number of the result.
	 */
	int startLNr;
	/**
	 * End line number of the result
	 */
	int endLNr;
	/**
	 * Start column index of the result.
	 */
	int startCol;
	/**
	 * End column index of the result.
	 */
	int endCol;
	/**
	 * Type of the error. I.e. "warning", "error" or "info".
	 */
	String logLvl;
	/**
	 * Type of the Ultimate result (i.e. CounterExample, Invariant, ...).
	 */
	String type;

	/**
	 * @return the shortDesc
	 */
	public String getShortDesc() {
		return shortDesc;
	}

	/**
	 * @return the longDesc
	 */
	public String getLongDesc() {
		return longDesc;
	}

	/**
	 * @return the startLNr
	 */
	public int getStartLNr() {
		return startLNr;
	}

	/**
	 * @return the endLNr
	 */
	public int getEndLNr() {
		return endLNr;
	}

	/**
	 * @return the startCol
	 */
	public int getStartCol() {
		return startCol;
	}

	/**
	 * @return the endCol
	 */
	public int getEndCol() {
		return endCol;
	}

	/**
	 * @return the logLvl
	 */
	public String getLogLvl() {
		return logLvl;
	}
	
	/**
	 * @return the logLvl
	 */
	public String getType() {
		return type;
	}

	@Override
	public String toString() {
		return "UltimateResult [shortDesc=" + shortDesc + ", longDesc="
				+ longDesc + ", startLNr=" + startLNr + ", endLNr=" + endLNr
				+ ", startCol=" + startCol + ", endCol=" + endCol + ", logLvl="
				+ logLvl + ", type=" + type + "]";
	}
	
	
}
