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

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.implementation.PSTVisitorWithResult;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTACSLComment;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTACSLNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTComment;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTConditionalBlock;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTDirective;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTIncludeDirective;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTLiteralRegion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTMacroExpansion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;

/**
 * A PST node function dispatcher.
 * 
 * @param <T>
 *            element type
 */
public final class PSTNodeFunctionDispatcher<T> {
	private final IPSTNodeFunction<T> mFunc;
	
	/**
	 * @param func
	 *            PST node function.
	 */
	public PSTNodeFunctionDispatcher(final IPSTNodeFunction<T> func) {
		mFunc = func;
	}
	
	/**
	 * @param node
	 *            PST node.
	 * @return result
	 */
	public T dispatch(final IPSTNode node) {
		final DispatchVisitor action = new DispatchVisitor();
		node.accept(action);
		return action.getResult().orElseGet(() -> mFunc.on(node));
	}
	
	/**
	 * PST visitor with result for dispatching.
	 */
	private final class DispatchVisitor extends PSTVisitorWithResult<T> {
		@Override
		public int visit(final IPSTComment comment) {
			setResult(mFunc.on(comment));
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IPSTConditionalBlock conditionalBlock) {
			setResult(mFunc.on(conditionalBlock));
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IPSTACSLComment acslComment) {
			setResult(mFunc.on(acslComment));
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IPSTACSLNode acslNode) {
			setResult(mFunc.on(acslNode));
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IPSTDirective directive) {
			setResult(mFunc.on(directive));
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IPSTIncludeDirective include) {
			setResult(mFunc.on(include));
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IPSTLiteralRegion literalRegion) {
			setResult(mFunc.on(literalRegion));
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IPSTMacroExpansion expansion) {
			setResult(mFunc.on(expansion));
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IPSTRegularNode node) {
			setResult(mFunc.on(node));
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IPSTTranslationUnit translationUnit) {
			setResult(mFunc.on(translationUnit));
			return PROCESS_ABORT;
		}
	}
}
