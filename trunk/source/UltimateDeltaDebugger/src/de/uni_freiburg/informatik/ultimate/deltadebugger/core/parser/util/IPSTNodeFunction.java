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
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTPreprocessorNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;

/**
 * Simulate a double dispatch function for an {@link IPSTNode} argument. Analogous to {@link IASTNodeFunction} for
 * consistency reasons.
 *
 * @param <T>
 *            returned type
 */
@FunctionalInterface
public interface IPSTNodeFunction<T> {
	/**
	 * @param comment
	 *            PST comment.
	 * @return result
	 */
	default T on(final IPSTComment comment) {
		return on((IPSTPreprocessorNode) comment);
	}
	
	/**
	 * @param acslComment
	 *            PST ACSL comment.
	 * @return result
	 */
	default T on(final IPSTACSLComment acslComment) {
		return on((IPSTComment) acslComment);
	}
	
	/**
	 * @param acslNode
	 *            PST ACSL node.
	 * @return result
	 */
	default T on(final IPSTACSLNode acslNode) {
		return on((IPSTNode) acslNode);
	}
	
	/**
	 * @param conditionalBlock
	 *            PST conditional block.
	 * @return result
	 */
	default T on(final IPSTConditionalBlock conditionalBlock) {
		return on((IPSTNode) conditionalBlock);
	}
	
	/**
	 * @param directive
	 *            PST directive.
	 * @return result
	 */
	default T on(final IPSTDirective directive) {
		return on((IPSTPreprocessorNode) directive);
	}
	
	/**
	 * @param includeDirective
	 *            PST include directive.
	 * @return result
	 */
	default T on(final IPSTIncludeDirective includeDirective) {
		return on((IPSTDirective) includeDirective);
	}
	
	/**
	 * @param literalRegion
	 *            PST literal region.
	 * @return result
	 */
	default T on(final IPSTLiteralRegion literalRegion) {
		return on((IPSTNode) literalRegion);
	}
	
	/**
	 * @param macroExpansion
	 *            PST macro expansion.
	 * @return result
	 */
	default T on(final IPSTMacroExpansion macroExpansion) {
		return on((IPSTPreprocessorNode) macroExpansion);
	}
	
	/**
	 * @param node
	 *            PST node.
	 * @return result
	 */
	T on(IPSTNode node);
	
	/**
	 * @param preprocessorNode
	 *            PST preprocessor node.
	 * @return result
	 */
	default T on(final IPSTPreprocessorNode preprocessorNode) {
		return on((IPSTNode) preprocessorNode);
	}
	
	/**
	 * @param node
	 *            PST regular node.
	 * @return result
	 */
	default T on(final IPSTRegularNode node) {
		return on((IPSTNode) node);
	}
	
	/**
	 * @param translationUnit
	 *            PST translation unit.
	 * @return result
	 */
	default T on(final IPSTTranslationUnit translationUnit) {
		return on((IPSTRegularNode) translationUnit);
	}
}
