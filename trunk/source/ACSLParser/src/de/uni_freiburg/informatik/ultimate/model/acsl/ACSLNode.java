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
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Predicate;

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
	 * The default location value used until it is explicitly set.
	 */
	public static final ACSLSourceLocation INVALID_LOCATION = new ACSLSourceLocation(-1, -1, -1, -1);

	// do not rename this field as auto-generated subclasses depend on it
	protected static final Map<Class<?>, Predicate<ACSLNode>> VALIDATORS = new HashMap<>();

	/**
	 * The list of children.
	 */
	private final List<ACSLNode> mChildren = new ArrayList<>();
	/**
	 * File Name.
	 */
	private String mFileName;
	/**
	 * The location in the source code.
	 */
	private ACSLSourceLocation mLocation = INVALID_LOCATION;

	/**
	 * Getter for the starting line number of this ACSL comment.
	 * 
	 * @return the starting line number of the ACSL-comment.
	 */
	public int getStartingLineNumber() {
		return mLocation.getStartLine();
	}

	/**
	 * Getter for the ending line number of this ACSL comment.
	 *
	 * @return the ending line number of the ACSL-comment.
	 */
	public int getEndingLineNumber() {
		return mLocation.getEndLine();
	}

	/**
	 * Returns a list of the nodes children.
	 * 
	 * @return list of children.
	 */
	public List<ACSLNode> getOutgoingNodes() {
		return mChildren;
	}

	/**
	 * Returns the file name.
	 * 
	 * @return the fileName
	 */
	public String getFileName() {
		return mFileName;
	}

	/**
	 * Sets the file name.
	 * 
	 * @param fileName
	 *            the fileName to set
	 */
	public void setFileName(final String fileName) {
		mFileName = fileName;
	}

	/**
	 * Getter for the location.
	 *
	 * @return the location of this node
	 */
	public ACSLSourceLocation getLocation() {
		return mLocation;
	}

	/**
	 * Sets the location.
	 *
	 * @param location
	 *            the location to set
	 */
	public void setLocation(final ACSLSourceLocation location) {
		mLocation = location;
	}

	/**
	 * Accepts a visitor and starts a DFS traversal of the AST.
	 * 
	 * @param visitor
	 *            visitor
	 */
	public abstract void accept(ACSLVisitor visitor);

	/**
	 * @param visitor
	 *            visitor.
	 * @return ACSL node
	 */
	public abstract ACSLNode accept(ACSLTransformer visitor);

	/**
	 * Source location of a node.
	 */
	public static class ACSLSourceLocation {
		private static final char SLASH = '/';

		private final int mStartLine;
		private final int mStartColumn;
		private final int mEndLine;
		private final int mEndColumn;

		/**
		 * @param startLine
		 *            Start line.
		 * @param startColumn
		 *            start column
		 * @param endLine
		 *            end line
		 * @param endColumn
		 *            end column
		 */
		public ACSLSourceLocation(final int startLine, final int startColumn, final int endLine, final int endColumn) {
			mStartLine = startLine;
			mStartColumn = startColumn;
			mEndLine = endLine;
			mEndColumn = endColumn;
		}

		public int getStartLine() {
			return mStartLine;
		}

		public int getStartColumn() {
			return mStartColumn;
		}

		public int getEndLine() {
			return mEndLine;
		}

		public int getEndColumn() {
			return mEndColumn;
		}

		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			// @formatter:off
			builder.append('[')
					.append(mStartLine)
					.append(SLASH)
					.append(mStartColumn)
					.append('-')
					.append(mEndLine)
					.append(SLASH)
					.append(mEndColumn)
					.append(']');
			// @formatter:on
			return builder.toString();
		}
	}
}
