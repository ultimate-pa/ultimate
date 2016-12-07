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
import java.util.List;

import org.eclipse.cdt.core.dom.ast.ASTNodeProperty;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTExpressionList;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTInitializerList;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorElifStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorElseStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorEndifStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfdefStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfndefStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorMacroDefinition;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTStandardFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IBinding;
import org.eclipse.cdt.core.parser.IToken;

/**
 * Utility class for AST nodes.
 */
public final class ASTNodeUtils {
	private ASTNodeUtils() {
		// utility class
	}
	
	/**
	 * @param astNode
	 *            AST node.
	 * @return array of AST child nodes
	 */
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
	
	/**
	 * @param astNode
	 *            AST node.
	 * @return property of child nodes
	 */
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
	
	/**
	 * @param node
	 *            AST node.
	 * @return {@code true} iff node is a conditional preprocessor statement
	 */
	public static boolean isConditionalPreprocessorStatement(final IASTNode node) {
		return node instanceof IASTPreprocessorIfStatement || node instanceof IASTPreprocessorIfdefStatement
				|| node instanceof IASTPreprocessorIfndefStatement || node instanceof IASTPreprocessorElseStatement
				|| node instanceof IASTPreprocessorElifStatement || node instanceof IASTPreprocessorEndifStatement;
	}
	
	/**
	 * @param node
	 *            AST node.
	 * @return {@code true} iff node is a conditional preprocessor statement that was taken
	 */
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
	
	/**
	 * @param simpleDeclaration
	 *            AST simple declaration.
	 * @return {@code true} iff declaration has references
	 */
	public static boolean hasReferences(final IASTSimpleDeclaration simpleDeclaration) {
		return Arrays.stream(simpleDeclaration.getDeclarators()).anyMatch(ASTNodeUtils::hasReferences);
	}
	
	/**
	 * @param functionDefinition
	 *            AST function definition.
	 * @return {@code true} iff function definition has references
	 */
	public static boolean hasReferences(final IASTFunctionDefinition functionDefinition) {
		return hasReferences(functionDefinition.getDeclarator());
	}
	
	/**
	 * @param macroDefintion
	 *            AST macro definition.
	 * @return {@code true} iff macro definition has references
	 */
	public static boolean hasReferences(final IASTPreprocessorMacroDefinition macroDefintion) {
		final IASTName astName = macroDefintion.getName();
		return astName != null && hasReferences(astName);
	}
	
	/**
	 * @param declarator
	 *            AST declarator.
	 * @return {@code true} iff declarator has references
	 */
	public static boolean hasReferences(final IASTDeclarator declarator) {
		if (hasReferences(declarator.getName())) {
			return true;
		}
		// Check each nested declarator for being unreferenced as well
		IASTDeclarator nested = declarator.getNestedDeclarator();
		while (nested != null) {
			if (hasReferences(nested.getName())) {
				return true;
			}
			nested = nested.getNestedDeclarator();
		}
		return false;
	}
	
	/**
	 * @param astName
	 *            AST name.
	 * @return {@code true} iff name has references
	 */
	public static boolean hasReferences(final IASTName astName) {
		final IBinding binding = astName.resolveBinding();
		final IASTName[] names = astName.getTranslationUnit().getReferences(binding);
		return names.length != 0;
	}
	
	public static boolean isFunctionPrototype(IASTSimpleDeclaration declaration) {
		final IASTDeclSpecifier declSpecifier = declaration.getDeclSpecifier();
		if (declSpecifier.getStorageClass() == IASTDeclSpecifier.sc_typedef) {
			return false;
		}

		if (declaration.getDeclarators().length != 1) {
			return false;
		}

		IASTDeclarator declarator = declaration.getDeclarators()[0];
		while (declarator instanceof IASTFunctionDeclarator) {
			if (declarator.getNestedDeclarator() != null) {
				declarator = declarator.getNestedDeclarator();
				continue;
			}
			// not a prototype if there is a pointer operator
			if (declarator.getPointerOperators().length != 0) {
				break;
			}
			return true;
		}

		return false;
	}

	public static boolean isTypedef(IASTSimpleDeclaration declaration) {
		final IASTDeclSpecifier declSpecifier = declaration.getDeclSpecifier();
		return declSpecifier.getStorageClass() == IASTDeclSpecifier.sc_typedef;
	}

	public static IASTName getNestedDeclaratorName(IASTDeclarator declarator) {
		IASTDeclarator current = declarator;
		while (current.getNestedDeclarator() != null) {
			current = current.getNestedDeclarator();
		}
		return current.getName();
	}

	public static List<Integer> getRequiredDeclSpecifierTokens(final IASTDeclSpecifier declSpecifier) {
		final List<Integer> requiredTokens = new ArrayList<>();
		int storageClass = declSpecifier.getStorageClass();
		switch (storageClass) {
		case IASTDeclSpecifier.sc_typedef:
			requiredTokens.add(IToken.t_typedef);
			break;
		case IASTDeclSpecifier.sc_extern:
			requiredTokens.add(IToken.t_extern);
			break;
		case IASTDeclSpecifier.sc_static:
			requiredTokens.add(IToken.t_static);
			break;
		case IASTDeclSpecifier.sc_auto:
			requiredTokens.add(IToken.t_auto);
			break;
		case IASTDeclSpecifier.sc_register:
			requiredTokens.add(IToken.t_register);
			break;
		case IASTDeclSpecifier.sc_mutable:
			requiredTokens.add(IToken.t_mutable);
			break;
		default:
			break;
		}
		if (declSpecifier.isConst()) {
			requiredTokens.add(IToken.t_const);
		}
		if (declSpecifier.isVolatile()) {
			requiredTokens.add(IToken.t_volatile);
		}
		if (declSpecifier.isRestrict()) {
			requiredTokens.add(IToken.t_restrict);
		}
		if (declSpecifier.isInline()) {
			requiredTokens.add(IToken.t_inline);
		}

		return requiredTokens;
	}
}
