/**
 * Basic class for the ACSL-AST. Every AST node extends this one.
 */
package de.uni_freiburg.informatik.ultimate.model.acsl;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLVisitor;

/**
 * @author Markus Lindenmann
 * @author Stefan Wissert
 * @author Oleksii Saukh
 * @date 30.01.2012
 */
public abstract class ACSLNode {
	/**
	 * The starting line number of this ACSL comment.
	 */
	private int startingLineNumber;
	/**
	 * The ending line number of this ACSL comment.
	 */
	private int endingLineNumber;
	/**
	 * The list of children.
	 */
	private List<Object> children = new ArrayList<Object>();
	/**
	 * File Name.
	 */
	private String fileName;

	/**
	 * Getter for the starting line number of this ACSL comment.
	 * 
	 * @return the starting line number of the ACSL-comment.
	 */
	public int getStartingLineNumber() {
		return startingLineNumber;
	}

	/**
	 * Setter for the starting line number of this ACSL comment.
	 * 
	 * @param startingLineNumber
	 *            the starting line number of the ACSL-comment.
	 */
	public void setStartingLineNumber(int startingLineNumber) {
		this.startingLineNumber = startingLineNumber;
	}

	/**
	 * Getter for the ending line number of this ACSL comment.
	 * 
	 * @return the ending line number of the ACSL-comment.
	 */
	public int getEndingLineNumber() {
		return endingLineNumber;
	}

	/**
	 * Setter for the ending line number of this ACSL comment.
	 * 
	 * @param endingLineNumber
	 *            the ending line number of the ACSL-comment.
	 */
	public void setEndingLineNumber(int endingLineNumber) {
		this.endingLineNumber = endingLineNumber;
	}

	/**
	 * Returns a list of the nodes children.
	 * 
	 * @return list of children.
	 */
	public List<Object> getChildren() {
		return children;
	}

	/**
	 * Returns the file name.
	 * 
	 * @return the fileName
	 */
	public String getFileName() {
		return fileName;
	}

	/**
	 * Sets the file name.
	 * 
	 * @param fileName
	 *            the fileName to set
	 */
	public void setFileName(String fileName) {
		this.fileName = fileName;
	}

	/**
	 * Accepts a visitor and starts a dfs traversal of the AST.
	 * 
	 * @param visitor
	 */
	public abstract void accept(ACSLVisitor visitor);

}
