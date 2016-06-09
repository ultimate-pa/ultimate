/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ACSLParser plug-in.
 * 
 * The ULTIMATE ACSLParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ACSLParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ACSLParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ACSLParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ACSLParser plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * Basic class for the ACSL-AST. Every AST node extends this one.
 */
package de.uni_freiburg.informatik.ultimate.model.acsl;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLTransformer;
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
	private final List<Object> children = new ArrayList<Object>();
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
	
	public abstract ACSLNode accept(ACSLTransformer visitor);

}
