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

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import org.eclipse.cdt.core.dom.ast.ASTNodeProperty;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTStandardFunctionDeclarator;
import org.eclipse.cdt.core.parser.IToken;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTGapVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTLiteralRegion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.TokenCollector.Token;

/**
 * Utility class to collect information about all comma separated children and the corresponding comma locations.
 * Implementation notes: By checking the "gaps" in the PST we can easily find tokens between nodes without preprocessing
 * the source text. Only requirement is that all preprocessor directives and comments actually exist in the PST.
 */
public final class CommaSeparatedChildFinder {
	private CommaSeparatedChildFinder() {
		// utility class
	}
	
	/**
	 * Find list of comma separated children of the given node identified by the given node property.
	 *
	 * @param parentNode
	 *            parent node that may have comma separated children
	 * @param childProperty
	 *            property to identify the child nodes
	 * @return sorted list of all child nodes with comma location
	 */
	public static List<CommaSeparatedChild> run(final IPSTRegularNode parentNode, final ASTNodeProperty childProperty) {
		final CommaSeparatedChildFinder.Visitor instance = new Visitor(parentNode, childProperty);
		GapVisitor.invokeAccept(parentNode, instance);
		return instance.mResult;
	}
	
	/**
	 * Find list of comma separated children of the given node identified by the given node property. This method also
	 * checks for a varargs function and adds a dummy entry for the "..." token.
	 *
	 * @param parentNode
	 *            parent node that may have comma separated children
	 * @param childProperty
	 *            property to identify the child nodes
	 * @return sorted list of all child nodes with comma location
	 */
	public static List<CommaSeparatedChild> runWithVarArgsSupport(final IPSTRegularNode parentNode,
			final ASTNodeProperty childProperty) {
		final CommaSeparatedChildFinder.Visitor instance = new Visitor(parentNode, childProperty);
		GapVisitor.invokeAccept(parentNode, instance);

		// Add dummy entry for varargs function parameters
		if (childProperty == IASTStandardFunctionDeclarator.FUNCTION_PARAMETER
				&& ((IASTStandardFunctionDeclarator) parentNode.getAstNode()).takesVarArgs()) {
			final List<Token> tokens = TokenCollector.collect(parentNode);
			final Token ellipsis = tokens.stream().filter(t -> t.getType() == IToken.tELLIPSIS).findAny().orElse(null);
			instance.mResult.add(new CommaSeparatedChild(null, ellipsis));
		}

		return instance.mResult;
	}
	
	/**
	 * PST gap visitor.
	 */
	private static final class Visitor implements IPSTGapVisitor {
		private final IPSTRegularNode mParentNode;
		private final ASTNodeProperty mChildProperty;
		private final List<CommaSeparatedChild> mResult = new ArrayList<>();
		
		private Visitor(final IPSTRegularNode parentNode, final ASTNodeProperty childProperty) {
			mParentNode = Objects.requireNonNull(parentNode);
			mChildProperty = Objects.requireNonNull(childProperty);
		}
		
		@Override
		public int defaultLeave(final IPSTNode node) {
			for (final IASTNode child : node.getUnexpandedChildNodes()) {
				if (child.getPropertyInParent().equals(mChildProperty)) {
					mResult.add(new CommaSeparatedChild(child, null));
				}
			}
			return PROCESS_CONTINUE;
		}
		
		@Override
		public int visit(final IPSTLiteralRegion literalRegion) {
			// Also add ast nodes from literal regions (but don't collect commas)
			defaultLeave(literalRegion);
			return PROCESS_SKIP;
		}
		
		@Override
		public int visit(final IPSTRegularNode node) {
			if (node.equals(mParentNode)) {
				return PROCESS_CONTINUE;
			}
			if (node.getAstNode().getPropertyInParent().equals(mChildProperty)) {
				mResult.add(new CommaSeparatedChild(node.getAstNode(), node));
			}
			return PROCESS_SKIP;
		}
		
		@Override
		public int visitGap(final int offset, final int endOffset) {
			final String text = mParentNode.getSource().getText(offset, endOffset);
			if (!text.trim().startsWith(",")) {
				return PROCESS_CONTINUE;
			}
			
			// Store the position of the first comma encountered after each
			// element
			if (!mResult.isEmpty()) {
				final CommaSeparatedChild previousElement = mResult.get(mResult.size() - 1);
				if (previousElement.mNextCommaLocation == null) {
					final int commaOffset = offset + text.indexOf(',');
					previousElement.mNextCommaLocation =
							mParentNode.getSource().newSourceRange(commaOffset, commaOffset + 1);
				}
			}
			return PROCESS_CONTINUE;
		}
	}
}
