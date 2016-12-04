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

/**
 * A node that corresponds to a source range that is processed by the preprocessor, e.g. a comment, a directive or macro
 * expansion. IASTNode derived types exist and getASTNode() is never null, but in contrast to IPSTRegularNodes, these
 * IASTNodes are not part of original tree. This is because in general these nodes may occur anywhere and overlap
 * regular node boundaries arbitrarily.
 * Note that the PST-node exist only if no non-descendents share the same source range, otherwise the source range and
 * IASTNodes would have been marked by an overlapping block. Unfortunately, rewriting includes and macro expansions is
 * still tricky, because even though no non-descendant nodes share the source range, the parent may still share
 * individual tokens:
 *
 * <pre>
 * {@code
 * #define COMMON_MACRO 1
 * int a = COMMON_MACRO + 2;
 *
 * #define BAD_MACRO 1 +
 * int b = BAD_MACRO 2;
 * }
 * </pre>
 *
 * The AST will contain a binary expression with two literal nodes as children. Both macro expansions have the literal
 * expression of 1 as unexpanded child nodes, but replacing BAD_MACRO by another expression will remove the operand
 * token and cause a syntax error.
 */
public interface IPSTPreprocessorNode extends IPSTNode {
	// empty super interface
}
