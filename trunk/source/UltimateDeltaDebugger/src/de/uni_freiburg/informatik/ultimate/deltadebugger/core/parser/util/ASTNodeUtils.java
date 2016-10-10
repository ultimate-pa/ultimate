package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util;

import org.eclipse.cdt.core.dom.ast.ASTNodeProperty;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTExpressionList;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerList;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorElifStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorElseStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorEndifStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfdefStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfndefStatement;
import org.eclipse.cdt.core.dom.ast.IASTStandardFunctionDeclarator;

public class ASTNodeUtils {

	public static IASTNode[] getCommaSeparatedChildNodes(final IASTNode astNode) {
		if (astNode instanceof IASTStandardFunctionDeclarator) {
			return ((IASTStandardFunctionDeclarator) astNode).getParameters();
		} else if (astNode instanceof IASTExpressionList) {
			return ((IASTExpressionList) astNode).getExpressions();
		} else if (astNode instanceof IASTInitializerList) {
			return ((IASTInitializerList) astNode).getClauses();
		} else if (astNode instanceof IASTFunctionCallExpression) {
			return ((IASTFunctionCallExpression) astNode).getArguments();
		} else if (astNode instanceof IASTEnumerationSpecifier) {
			return ((IASTEnumerationSpecifier) astNode).getEnumerators();
		}
		return new IASTNode[0];
	}

	public static ASTNodeProperty getPropertyOfCommaSeparatedChildNodes(final IASTNode astNode) {
		if (astNode instanceof IASTStandardFunctionDeclarator) {
			return IASTStandardFunctionDeclarator.FUNCTION_PARAMETER;
		} else if (astNode instanceof IASTExpressionList) {
			return IASTExpressionList.NESTED_EXPRESSION;
		} else if (astNode instanceof IASTInitializerList) {
			return IASTInitializerList.NESTED_INITIALIZER;
		} else if (astNode instanceof IASTFunctionCallExpression) {
			return IASTFunctionCallExpression.ARGUMENT;
		} else if (astNode instanceof IASTEnumerationSpecifier) {
			return IASTEnumerationSpecifier.ENUMERATOR;
		}
		return null;
	}

	public static boolean isConditionalPreprocessorStatement(final IASTNode node) {
		return node instanceof IASTPreprocessorIfStatement || node instanceof IASTPreprocessorIfdefStatement
				|| node instanceof IASTPreprocessorIfndefStatement || node instanceof IASTPreprocessorElseStatement
				|| node instanceof IASTPreprocessorElifStatement || node instanceof IASTPreprocessorEndifStatement;
	}

	public static boolean isConditionalPreprocessorStatementTaken(final IASTNode node) {
		if (node instanceof IASTPreprocessorIfStatement) {
			return ((IASTPreprocessorIfStatement) node).taken();
		} else if (node instanceof IASTPreprocessorIfdefStatement) {
			return ((IASTPreprocessorIfdefStatement) node).taken();
		} else if (node instanceof IASTPreprocessorIfndefStatement) {
			return ((IASTPreprocessorIfndefStatement) node).taken();
		} else if (node instanceof IASTPreprocessorElseStatement) {
			return ((IASTPreprocessorElseStatement) node).taken();
		} else if (node instanceof IASTPreprocessorElifStatement) {
			return ((IASTPreprocessorElifStatement) node).taken();
		}

		return false;
	}

	private ASTNodeUtils() {
	}
}
