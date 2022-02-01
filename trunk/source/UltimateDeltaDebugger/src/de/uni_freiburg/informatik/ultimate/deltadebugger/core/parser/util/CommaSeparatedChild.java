/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;

/**
 * A child node in a comma separated list together with the location of the next comma (if known).
 */
public class CommaSeparatedChild {
	protected ISourceRange mNextCommaLocation;
	private final IASTNode mAstNode;
	private final ISourceRange mNodeLocation;

	/**
	 * @param astNode
	 *            The child node in the AST.
	 * @param nodeLocation
	 *            The corresponding node location if known.
	 */
	public CommaSeparatedChild(final IASTNode astNode, final ISourceRange nodeLocation) {
		mAstNode = astNode;
		mNodeLocation = nodeLocation;
	}

	/**
	 * @return IASTNode (null iff this is a dummy entry for a varargs placeholder).
	 */
	public IASTNode astNode() {
		return mAstNode;
	}

	/**
	 * @return Location of the first comma encountered after the child node. null if no comma was found.
	 */
	public ISourceRange nextCommaLocation() {
		return mNextCommaLocation;
	}

	/**
	 * @return Location of a regular PST node corresponding to the IASTNode if it exists. If this is an entry for a
	 *         varargs placeholder the location of "..." token. Otherwise null of not found.
	 */
	public ISourceRange nodeLocation() {
		return mNodeLocation;
	}

	@Override
	public String toString() {
		return "CommaSeparatedChild [astNode=" + mAstNode + ", nodeLocation=" + mNodeLocation + ", nextCommaLocation="
				+ mNextCommaLocation + "]";
	}
}
