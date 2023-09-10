/**
 * Represents an Ultimate Result entry, that can be represented to the client
 * and easily sent via JSON and interpreted with JS. This means i.e. you should
 * avoid complex data structures in this class!
 */
package de.uni_freiburg.informatik.ultimate.web.backend.dto;

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
	private String shortDesc;
	/**
	 * Long description, shown in a table or other listing.
	 */
	private String longDesc;
	/**
	 * Start line number of the result.
	 */
	private int startLNr;
	/**
	 * End line number of the result
	 */
	private int endLNr;
	/**
	 * Start column index of the result.
	 */
	private int startCol;
	/**
	 * End column index of the result.
	 */
	private int endCol;
	/**
	 * Type of the error. I.e. "warning", "error" or "info".
	 */
	private String logLvl;
	/**
	 * Type of the Ultimate result (i.e. CounterExample, Invariant, ...).
	 */
	private String type;

	public String getShortDesc() {
		return shortDesc;
	}

	public String getLongDesc() {
		return longDesc;
	}

	public int getStartLNr() {
		return startLNr;
	}

	public int getEndLNr() {
		return endLNr;
	}

	public int getStartCol() {
		return startCol;
	}

	public int getEndCol() {
		return endCol;
	}

	public String getLogLvl() {
		return logLvl;
	}

	public String getType() {
		return type;
	}

	public void setShortDesc(final String shortDesc) {
		this.shortDesc = shortDesc;
	}

	public void setLongDesc(final String longDesc) {
		this.longDesc = longDesc;
	}

	public void setStartLNr(final int startLNr) {
		this.startLNr = startLNr;
	}

	public void setEndLNr(final int endLNr) {
		this.endLNr = endLNr;
	}

	public void setStartCol(final int startCol) {
		this.startCol = startCol;
	}

	public void setEndCol(final int endCol) {
		this.endCol = endCol;
	}

	public void setLogLvl(final String logLvl) {
		this.logLvl = logLvl;
	}

	public void setType(final String type) {
		this.type = type;
	}

	@Override
	public String toString() {
		return "UltimateResult [shortDesc=" + shortDesc + ", longDesc=" + longDesc + ", startLNr=" + startLNr
				+ ", endLNr=" + endLNr + ", startCol=" + startCol + ", endCol=" + endCol + ", logLvl=" + logLvl
				+ ", type=" + type + "]";
	}

}
