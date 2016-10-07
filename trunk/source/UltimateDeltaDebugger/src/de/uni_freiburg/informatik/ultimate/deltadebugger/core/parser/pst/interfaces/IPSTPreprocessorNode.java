package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces;

/**
 * A node that corresponds to a source range that is processed by the
 * preprocessor, e.g. a comment, a directive or macro expansion.
 * IASTNode derived types exist and getASTNode() is never null, but in contrast
 * to IPSTRegularNodes, these IASTNodes are not part of original tree. This is
 * because in general these nodes may occur anywhere and overlap regular node
 * boundaries arbitrarily.
 * 
 * Note that the PST-node exist only if no non-descendents share the same source
 * range, otherwise the source range and IASTNodes would have been marked by an
 * overlapping block. Unfortunately, rewriting includes and macro expansions is
 * still tricky, because even though no non-descendant nodes share the source
 * range, the parent may still share individual tokens:
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
 * The AST will contain a binary expression with two literal nodes as children.
 * Both macro expansions have the literal expression of 1 as unexpanded child
 * nodes, but replacing BAD_MACRO by another expression will remove the operand
 * token and cause a syntax error.
 * 
 */
public interface IPSTPreprocessorNode extends IPSTNode {
	
}