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
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.implementation;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;

/**
 * Regular PST node.
 */
public class PSTRegularNode extends PSTNode implements IPSTRegularNode {
	/**
	 * @param source
	 *            Source document.
	 * @param location
	 *            source range
	 * @param astNode
	 *            AST node
	 */
	public PSTRegularNode(final ISourceDocument source, final ISourceRange location, final IASTNode astNode) {
		super(source, location, astNode);
	}
	
	@Override
	int dispatchLeave(final IPSTVisitor action) {
		return action.leave(this);
	}
	
	@Override
	int dispatchVisit(final IPSTVisitor action) {
		return action.visit(this);
	}
	
	@SuppressWarnings("squid:S1698")
	@Override
	public IPSTRegularNode findRegularChild(final IASTNode astNode) {
		final PSTVisitorWithResult<IPSTRegularNode> action = new PSTVisitorWithResult<IPSTRegularNode>() {
			@Override
			public int visit(final IPSTRegularNode node) {
				if (PSTRegularNode.this.equals(node)) {
					return PROCESS_CONTINUE;
				} else if (node.getAstNode() == astNode) {
					setResult(node);
					return PROCESS_ABORT;
				}
				return PROCESS_SKIP;
			}
		};
		accept(action);
		return action.getResult().orElse(null);
	}
}
