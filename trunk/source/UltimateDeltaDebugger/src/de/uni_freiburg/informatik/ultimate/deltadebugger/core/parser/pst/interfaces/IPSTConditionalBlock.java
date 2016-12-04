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
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces;

import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;

/**
 * A conditional block groups nodes within a conditional preprocessor region, i.e. the source text enclosed in
 * #if/#else/#endif directives. Only nodes in the active branch are children of this node.
 */
public interface IPSTConditionalBlock extends IPSTNode {
	/**
	 * @return Active branch location.
	 */
	ISourceRange getActiveBranchLocation();
	
	@Override
	default IASTNode getAstNode() {
		return null;
	}
	
	/**
	 * @return List of conditional directives.
	 */
	List<IPSTDirective> getConditionalDirectives();
	
	/**
	 * @return {@code true} iff the conditional block has an active branch.
	 */
	boolean hasActiveBranch();
}
