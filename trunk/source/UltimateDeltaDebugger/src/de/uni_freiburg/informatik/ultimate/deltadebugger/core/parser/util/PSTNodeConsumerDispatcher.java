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
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;

/**
 * A PST node consumer dispatcher.
 */
public final class PSTNodeConsumerDispatcher {
	
	private final IPSTNodeConsumer mConsumer;
	
	/**
	 * @param consumer
	 *            PST node consumer.
	 */
	public PSTNodeConsumerDispatcher(final IPSTNodeConsumer consumer) {
		mConsumer = consumer;
	}
	
	/**
	 * @param node
	 *            PST node.
	 */
	public void dispatch(final IPSTNode node) {
		node.accept(new DispatchVisitor());
	}
	
	/**
	 * The visitor for dispatching.
	 */
	private final class DispatchVisitor implements IPSTVisitor {
		public DispatchVisitor() {
			// empty constructor
		}
		
		@Override
		public int defaultVisit(final IPSTNode node) {
			mConsumer.on(node);
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IPSTComment comment) {
			mConsumer.on(comment);
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IPSTACSLComment acslComment) {
			mConsumer.on(acslComment);
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IPSTACSLNode acslNode) {
			mConsumer.on(acslNode);
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IPSTConditionalBlock conditionalBlock) {
			mConsumer.on(conditionalBlock);
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IPSTDirective directive) {
			mConsumer.on(directive);
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IPSTIncludeDirective include) {
			mConsumer.on(include);
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IPSTLiteralRegion literalRegion) {
			mConsumer.on(literalRegion);
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IPSTMacroExpansion expansion) {
			mConsumer.on(expansion);
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IPSTRegularNode node) {
			mConsumer.on(node);
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IPSTTranslationUnit translationUnit) {
			mConsumer.on(translationUnit);
			return PROCESS_ABORT;
		}
	}
}
