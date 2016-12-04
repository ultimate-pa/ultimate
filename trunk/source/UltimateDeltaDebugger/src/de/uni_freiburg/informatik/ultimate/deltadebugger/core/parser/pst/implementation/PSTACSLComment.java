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

import org.eclipse.cdt.core.dom.ast.IASTComment;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTACSLComment;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceDocumentLocationPrinter;

/**
 * PST node for ACSL comment wrapping.
 */
public class PSTACSLComment extends PSTComment implements IPSTACSLComment {
	/**
	 * @param source
	 *            Source document.
	 * @param location
	 *            source range
	 * @param comment
	 *            AST comments
	 */
	public PSTACSLComment(final ISourceDocument source, final ISourceRange location, final IASTComment comment) {
		super(source, location, comment);
	}
	
	@Override
	int dispatchLeave(final IPSTVisitor action) {
		return action.leave(this);
	}
	
	@Override
	int dispatchVisit(final IPSTVisitor action) {
		return action.visit(this);
	}
	
	@Override
	public String toString() {
		final String text = getSourceText().replace("\n", "\\n").replace("\r", "");
		final StringBuilder sb = new StringBuilder();
		sb.append(this.getClass().getSimpleName());
		sb.append(" (");
		if (text.length() > ASTNODE_TOSTRING_LIMIT) {
			sb.append(text, 0, ASTNODE_TOSTRING_LIMIT).append("...");
		} else {
			sb.append(text);
		}
		sb.append(")");
		sb.append(" [");
		SourceDocumentLocationPrinter.appendTo(mSource, mOffset, mEndOffset, sb);
		sb.append("]");
		return sb.toString();
	}
}
