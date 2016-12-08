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
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.ToolFactory;
import org.eclipse.cdt.core.dom.ast.ASTNodeProperty;
import org.eclipse.cdt.core.dom.ast.IASTArrayModifier;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclarationStatement;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTLabelStatement;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IBasicType;
import org.eclipse.cdt.core.dom.ast.IPointerType;
import org.eclipse.cdt.core.dom.ast.IType;
import org.eclipse.cdt.core.formatter.CodeFormatter;
import org.eclipse.cdt.core.formatter.DefaultCodeFormatterConstants;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.text.edits.MalformedTreeException;
import org.eclipse.text.edits.TextEdit;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTComment;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTMacroExpansion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

/**
 * Utility class for rewrites.
 */
public final class RewriteUtils {
	private static final int MAX_PRETTY_PRINTED_LENGTH = 10_000;
	
	private RewriteUtils() {
		// utility class
	}
	
	/**
	 * Pretty print source code using the CDT code formatter. Seems to work without workspace and/or OSGi, but can cause
	 * extreme lags/freezes for larger inputs.
	 * Maybe this should be removed by something that removes redundant whitespace.
	 *
	 * @param input
	 *            source code
	 * @return pretty printed source code
	 */
	public static String debugPrettyPrintSourceCode(final String input) {
		// The formatter can be ridiculously slow for large inputs (possible
		// related to deeply nested expressions).
		// This is just a hack that reduces the chance to freeze.
		if (input.length() > MAX_PRETTY_PRINTED_LENGTH) {
			return removeMultipleEmptyLines(input);
		}
		
		final Map<String, String> options = DefaultCodeFormatterConstants.getDefaultSettings();
		final CodeFormatter formatter = ToolFactory.createDefaultCodeFormatter(options);
		final TextEdit edits = formatter.format(CodeFormatter.K_TRANSLATION_UNIT, input, 0, input.length(), 0, null);
		final IDocument doc = new Document(input);
		try {
			edits.apply(doc);
			return doc.get().replace("\t", "    ");
		} catch (MalformedTreeException | BadLocationException e) {
			return input;
		}
	}
	
	/**
	 * Deleting certain nodes from the source text may require a replacement with a whitespace to ensure that no
	 * enclosing tokens are joined.
	 *
	 * @param node
	 *            PST node
	 * @return string
	 */
	public static String getDeletionStringWithWhitespaces(final IPSTNode node) {
		// Deleteing comments and (function style) macro expansions
		// completely can cause problems if there are no whitespaces
		// to the left or right and tokens are joined.
		if (node instanceof IPSTComment || node instanceof IPSTMacroExpansion) {
			return " ";
		}
		// Not sure if there are other cases where a whitespace is required,
		// just use a space anywhere for now.
		return " ";
	}
	
	/**
	 * @param input
	 *            Input string.
	 * @return string without empty lines
	 */
	public static String removeMultipleEmptyLines(final String input) {
		return input.replaceAll("(?m)^(\\s*\r?\n){2,}", "\n");
	}
	
	/**
	 * Checks if the given replacement string is the same as the existing source text and would not have any effect.
	 *
	 * @param node
	 *            node
	 * @param replacementString
	 *            replacementString
	 * @return if replacement by the given string should be skipped
	 */
	public static boolean skipEquivalentReplacement(final IPSTNode node, final String replacementString) {
		// Do not replace something by itself
		// It would be better to compare tokens, but we can at least ignore
		// differences in whitespaces
		final String lhs = node.getSourceText().replaceAll("\\s+", " ");
		final String rhs = replacementString.replaceAll("\\s+", " ");
		return lhs.equals(rhs);
	}
	
	/**
	 * If any replacement already matches the current source text, skip ALL the other alternatives, not just the one
	 * that matches. This is important to not endlessly switch between two alternatives that are both possible in
	 * repeated HDD applications.
	 * 
	 * @param node
	 *            PST node to be replacement
	 * @param replacementStrings
	 *            list of replacements to be tested in the given order
	 * @return list of valid replacement strings
	 */
	public static List<String> removeEquivalentReplacements(final IPSTNode node,
			final List<String> replacementStrings) {
		final List<String> validReplacements = new ArrayList<>();
		for (final String replacement : replacementStrings) {
			if (RewriteUtils.skipEquivalentReplacement(node, replacement)) {
				break;
			}
			validReplacements.add(replacement);
		}
		return validReplacements;
	}
	
	/**
	 * @param expression
	 *            AST expression.
	 * @return list of minimal expression replacements
	 */
	public static List<String> getMinimalExpressionReplacements(final IASTExpression expression) {
		if (expression instanceof IASTLiteralExpression) {
			final IASTLiteralExpression literalExpression = (IASTLiteralExpression) expression;
			if (literalExpression.getKind() == IASTLiteralExpression.lk_float_constant) {
				return Arrays.asList(".0f");
			} else if (literalExpression.getKind() == IASTLiteralExpression.lk_string_literal) {
				return Arrays.asList("\"\"");
			}
		}
		
		// Prefer single element arrays over zero sized arrays
		if (expression.getPropertyInParent() == IASTArrayModifier.CONSTANT_EXPRESSION) {
			return Arrays.asList("1", "0");
		}
				
		final IType expressionType = expression.getExpressionType();
		if (expressionType instanceof IBasicType) {
			return Arrays.asList("0", "1");
		} else if (expressionType instanceof IPointerType) {
			return Arrays.asList("0");
		}
		
		return Collections.emptyList();
	}
	
	/**
	 * @param rewriter
	 *            Source rewriter.
	 * @param node
	 *            PST node
	 */
	public static void deleteNodeText(final SourceRewriter rewriter, final IPSTNode node) {
		rewriter.replace(node, getDeletionStringWithWhitespaces(node));
	}
	
	/**
	 * @param rewriter
	 *            Source rewriter.
	 * @param location
	 *            source range
	 */
	public static void replaceByWhitespace(final SourceRewriter rewriter, final ISourceRange location) {
		rewriter.replace(location, " ");
	}

	/**
	 * @param statement
	 *            Statement node.
	 * @return {@code true} iff the given statement must be replaced by ";" and cannot be deleted comepletely
	 */
	public static boolean isStatementRequired(final IASTStatement statement) {
		final ASTNodeProperty property = statement.getPropertyInParent();
		return property != IASTCompoundStatement.NESTED_STATEMENT && property != IASTLabelStatement.NESTED_STATEMENT;
	}

	public static boolean isSemicolonRequired(final IASTSimpleDeclaration declaration) {
		final ASTNodeProperty property = declaration.getPropertyInParent();
		if (property == IASTDeclarationStatement.DECLARATION) {
			return isStatementRequired((IASTStatement) declaration.getParent());
		}
		return false;
	}

	/**
	 * Checks for statements and declarations that need a ";" in order to be deleted.
	 * 
	 * @param node
	 *            PST node.
	 * @return String to use for deletion.
	 */
	public static String getReplacementStringForSafeDeletion(IPSTNode node) {
		final IASTNode astNode = node.getAstNode();
		if ((astNode instanceof IASTStatement && isStatementRequired((IASTStatement) astNode))
				|| (astNode instanceof IASTSimpleDeclaration && isSemicolonRequired((IASTSimpleDeclaration) astNode))) {
			return ";";
		}
		return getDeletionStringWithWhitespaces(node);
	}
	
}
