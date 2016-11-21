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
	 * The default location value used until it is explicitly set
	 */
	public static final ACSLSourceLocation INVALID_LOCATION = new ACSLSourceLocation(-1, -1, -1, -1);

	/**
	 * The list of children.
	 */
	private final List<Object> children = new ArrayList<>();
	/**
	 * File Name.
	 */
	private String fileName;
	/**
	 * The location in the source code.
	 */
	private ACSLSourceLocation location = INVALID_LOCATION;

	/**
	 * Getter for the starting line number of this ACSL comment.
	 * 
	 * @return the starting line number of the ACSL-comment.
	 */
	public int getStartingLineNumber() {
		return location.getStartLine();
	}

	/**
	 * Getter for the ending line number of this ACSL comment.
	 *
	 * @return the ending line number of the ACSL-comment.
	 */
	public int getEndingLineNumber() {
		return location.getEndLine();
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
	 * Getter for the location.
	 *
	 * @return the location of this node
	 */
	public ACSLSourceLocation getLocation() {
		return location;
	}

	/**
	 * Sets the location.
	 *
	 * @param location
	 *            the location to set
	 */
	public void setLocation(ACSLSourceLocation location) {
		this.location = location;
	}

	/**
	 * Accepts a visitor and starts a dfs traversal of the AST.
	 * 
	 * @param visitor
	 */
	public abstract void accept(ACSLVisitor visitor);

	public abstract ACSLNode accept(ACSLTransformer visitor);

	/**
	 * Source location of a node.
	 */
	public static class ACSLSourceLocation {
		final int startLine;
		final int startColumn;
		final int endLine;
		final int endColumn;

		public ACSLSourceLocation(int startLine, int startColumn, int endLine, int endColumn) {
			super();
			this.startLine = startLine;
			this.startColumn = startColumn;
			this.endLine = endLine;
			this.endColumn = endColumn;
		}

		public int getStartLine() {
			return startLine;
		}

		public int getStartColumn() {
			return startColumn;
		}

		public int getEndLine() {
			return endLine;
		}

		public int getEndColumn() {
			return endColumn;
		}

		@Override
		public String toString() {
			final StringBuilder sb = new StringBuilder();
			sb.append("[").append(startLine).append("/").append(startColumn).append("-").append(endLine).append("/")
					.append(endColumn).append("]");
			return sb.toString();
		}
	}
}
