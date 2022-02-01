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
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst;

import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTACSLComment;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTACSLNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;

/**
 * Expands IPSTACSLComment nodes to contain IPSTACSLNodes where possible.
 */
public final class PSTACSLBuilder implements IPSTVisitor {
	private final ILogger mLogger;
	/**
	 * Counter to detect if we are currently inside a function definition.
	 */
	private int mEnteredFunctionDefinitions;
	
	private PSTACSLBuilder(final ILogger logger) {
		mLogger = logger;
	}
	
	/**
	 * Expand all ACSL comments within the given PST node.
	 * 
	 * @param node
	 *            PST root node to expand nested ACSL comments in
	 * @param logger
	 *            logger
	 */
	public static void build(final IPSTNode node, final ILogger logger) {
		node.accept(new PSTACSLBuilder(logger));
	}
	
	@Override
	public int visit(final IPSTACSLComment acslComment) {
		// Try to parse it, if it doesn't work just continue
		final ACSLCommentParser parser = new ACSLCommentParser(acslComment, mEnteredFunctionDefinitions < 1, mLogger);
		final IPSTACSLNode pstNode = parser.parseAndCreatePst();
		if (pstNode != null) {
			acslComment.addChild(pstNode);
		}
		return PROCESS_SKIP;
	}
	
	@Override
	public int visit(final IPSTRegularNode node) {
		if (node.getAstNode() instanceof IASTFunctionDefinition) {
			++mEnteredFunctionDefinitions;
		}
		return PROCESS_CONTINUE;
	}
	
	@Override
	public int leave(final IPSTRegularNode node) {
		if (node.getAstNode() instanceof IASTFunctionDefinition) {
			--mEnteredFunctionDefinitions;
		}
		return PROCESS_CONTINUE;
	}
}
